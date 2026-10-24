// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Public dimensions, witness coordinates, and the mixed-field Polygero wire format.
//!
//! Geometry determines the lengths of H, Z, packed rows and Merkle nonces.
//! Each row contains its t queried values in transcript order, with rows consecutive
//! in memory and on the wire. Product-output rows are virtual: only x and y are
//! sent, and the verifier reconstructs z = x*y. Responses use full-field elements.
//! Packed row values use maximal runs selected by actual subfield membership.
//! Decoding restores ambient-field elements, so verification needs neither a
//! subfield-row bitmap nor prover sampling hints.
use std::io::{Error, ErrorKind, Result};

use super::{Digest, MerkleProof};
use crate::{core::algebra::SerializableField, runtime::algebra::Subfield};

/// Public dimensions of a nonrecursive invocation, selected by the caller.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PolygeroConfig {
    /// Dimension of ordinary row polynomials.
    pub k: usize,
    /// Batching-polynomial degree bound; each B_i has s+1 samples.
    pub s: usize,
    /// Number of committed oracle columns.
    pub n: usize,
    /// Distinct opened columns and random prefix samples reserved in each row.
    pub t: usize,
}

/// One product constraint w[x]*w[y]=w[z], using original witness indices.
/// Commitment creates a triple of row copies; linear batching later connects
/// each copy to its original witness value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PolygeroProductConstraint {
    pub x: usize,
    pub y: usize,
    pub z: usize,
}

/// Public counts used to validate proof shape and derive the committed row layout.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PolygeroGeometry {
    pub(crate) nw: usize,
    pub(crate) nq: usize,
    pub(crate) k: usize,
    pub(crate) s: usize,
    pub(crate) n: usize,
    pub(crate) t: usize,
}
impl PolygeroGeometry {
    pub(crate) fn sizes(&self) -> [usize; 6] {
        [self.nw, self.nq, self.k, self.s, self.n, self.t]
    }
    pub(crate) fn validate(&self) -> Result<()> {
        let invalid = || Error::new(ErrorKind::InvalidInput, "invalid Polygero geometry");
        if self.sizes().iter().any(|&x| x > (1 << 28))
            || self.k == 0
            || self.t >= self.k
            || self.t == 0
            || self.t > self.n
            || self.k.checked_add(self.s).is_none_or(|d| d > self.n)
            || self.k.checked_mul(2).is_none_or(|d| d > self.n)
            || (self.nq > 0 && self.k.div_ceil(2) <= self.t)
        {
            return Err(invalid());
        }
        self.nrow()
            .checked_mul(self.n)
            .filter(|&x| x <= (1 << 28))
            .ok_or_else(invalid)?;
        Ok(())
    }
    pub(crate) fn ordinary_rows(&self) -> usize {
        self.nw.div_ceil(self.ordinary_width())
    }
    /// Number of product groups, each represented by three rows x, y, z.
    pub(crate) fn product_groups(&self) -> usize {
        if self.nq == 0 {
            0
        } else {
            self.nq.div_ceil(self.product_width())
        }
    }
    pub(crate) fn data_rows(&self) -> usize {
        self.ordinary_rows() + 3 * self.product_groups()
    }
    pub(crate) fn nrow(&self) -> usize {
        self.data_rows() + 3
    }
    /// Rows carried in the proof; each product-output row is reconstructed from x and y.
    pub(crate) fn transmitted_rows(&self) -> usize {
        self.nrow() - self.product_groups()
    }
    pub(crate) fn response_lengths(&self) -> [usize; 2] {
        [self.k + self.s, 2 * self.k]
    }

    /// Witness slots in an ordinary row, after its random prefix.
    pub(crate) fn ordinary_width(&self) -> usize {
        self.k - self.t
    }

    /// Dimension of each product input polynomial; their product has dimension at most K.
    pub(crate) fn product_dimension(&self) -> usize {
        self.k.div_ceil(2)
    }

    /// Product slots in each group of two inputs and one output.
    pub(crate) fn product_width(&self) -> usize {
        self.product_dimension() - self.t
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PolygeroCommitment {
    pub(crate) root: Digest,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PolygeroProof<E> {
    /// Primary response H, dimension k+s, on the first k+s oracle nodes.
    pub(crate) h: Vec<E>,
    /// Arithmetic response Z, dimension at most 2k, on the first 2k oracle nodes.
    pub(crate) z: Vec<E>,
    /// Selected oracle values, packed by row, omitting virtual product-output rows.
    /// Order: u, m, ordinary rows, product-input pairs x,y, then fstar.
    /// Each row has t entries in transcript query order, both in memory and on the wire.
    pub(crate) rows: Vec<E>,
    pub(crate) opening: MerkleProof,
}
fn invalid(message: &str) -> Error {
    Error::new(ErrorKind::InvalidData, message)
}
impl<E> PolygeroProof<E> {
    pub(crate) fn validate(&self, geom: &PolygeroGeometry) -> Result<()> {
        geom.validate()?;
        if [self.h.len(), self.z.len()] != geom.response_lengths()
            || self.rows.len() != geom.t * geom.transmitted_rows()
            || self.opening.nonce.len() != geom.t
            || self.opening.path.len()
                > geom.t * (geom.n.next_power_of_two().trailing_zeros() as usize + 1)
        {
            return Err(invalid("Polygero proof shape"));
        }
        Ok(())
    }
    /// Encode packed row values by actual membership, using alternating full-field
    /// and subfield runs. Responses retain their fixed full-field encoding.
    pub fn write<F: SerializableField<E = E>, SF: Subfield<E = E>>(
        &self,
        geom: &PolygeroGeometry,
        f: &F,
        sf: &SF,
    ) -> Result<Vec<u8>> {
        let mut out = Vec::new();
        self.write_to_buf(&mut out, geom, f, sf)?;
        Ok(out)
    }

    /// Append directly to a containing proof's buffer, avoiding a second copy
    /// of the complete Polygero encoding during Longfellow serialization.
    pub(crate) fn write_to_buf<F: SerializableField<E = E>, SF: Subfield<E = E>>(
        &self,
        out: &mut Vec<u8>,
        geom: &PolygeroGeometry,
        f: &F,
        sf: &SF,
    ) -> Result<()> {
        self.validate(geom)?;
        validate_codecs(f, sf)?;
        out.extend_from_slice(b"PLG7");
        for size in geom.sizes() {
            super::util::write_size_4bytes(out, size);
        }
        for values in [&self.h, &self.z] {
            for value in values {
                super::util::write_elt_field(out, value, f);
            }
        }
        write_rows(out, &self.rows, f, sf)?;
        self.opening.write_nonces(out);
        self.opening.write_path(out);
        Ok(())
    }
}

/// Decode self-describing row runs into ambient-field elements. No witness
/// boundary, row classification, or prover sampling policy is needed.
pub fn read<F: SerializableField, SF: Subfield<E = F::E>>(
    bytes: &mut &[u8],
    geom: &PolygeroGeometry,
    f: &F,
    sf: &SF,
) -> Result<PolygeroProof<F::E>> {
    geom.validate()?;
    validate_codecs(f, sf)?;
    if bytes.get(..4) != Some(b"PLG7") {
        return Err(invalid("Polygero version marker"));
    }
    *bytes = &bytes[4..];
    for expected in geom.sizes() {
        if super::util::read_size_4bytes(bytes)? != expected {
            return Err(invalid("Polygero geometry mismatch"));
        }
    }
    let lengths = geom.response_lengths();
    let count = lengths.iter().sum::<usize>();
    let opened_count = geom.t * geom.transmitted_rows();
    // Even the shortest encoding must contain all responses, compact rows,
    // at least one run header, the nonces, and the frontier length. Check this
    // before allocating vectors from the supplied dimensions.
    let needed = count
        .checked_mul(f.serialized_size_bytes())
        .and_then(|size| {
            opened_count
                .checked_mul(sf.serialized_size_bytes())?
                .checked_add(size)
        })
        .and_then(|size| (32 * geom.t).checked_add(size))
        .and_then(|size| size.checked_add(8))
        .ok_or_else(|| invalid("Polygero size overflow"))?;
    if bytes.len() < needed {
        return Err(Error::new(ErrorKind::UnexpectedEof, "Polygero fields"));
    }
    let mut values = |n| -> Result<Vec<F::E>> { (0..n).map(|_| read_field(bytes, f)).collect() };
    let h = values(lengths[0])?;
    let z = values(lengths[1])?;
    let rows = read_rows(bytes, opened_count, f, sf)?;
    let opening = read_opening(bytes, geom)?;
    Ok(PolygeroProof {
        h,
        z,
        rows,
        opening,
    })
}

/// Runs start with full-field values. An empty initial run selects subfield
/// values immediately; all later runs are nonempty and maximal by membership.
fn write_rows<F: SerializableField, SF: Subfield<E = F::E>>(
    out: &mut Vec<u8>,
    values: &[F::E],
    f: &F,
    sf: &SF,
) -> Result<()> {
    let mut index = 0;
    let mut subfield = false;
    while index < values.len() {
        let length = values[index..]
            .iter()
            .take_while(|value| sf.contains(value) == subfield)
            .count();
        super::util::write_size_4bytes(out, length);
        for value in &values[index..index + length] {
            if subfield {
                super::util::write_subfield_elt(out, value, sf)?;
            } else {
                super::util::write_elt_field(out, value, f);
            }
        }
        index += length;
        subfield = !subfield;
    }
    Ok(())
}

/// Enforce a unique run encoding: only the initial full-field run may be empty,
/// and every value must belong to the class declared by its run.
fn read_rows<F: SerializableField, SF: Subfield<E = F::E>>(
    bytes: &mut &[u8],
    count: usize,
    f: &F,
    sf: &SF,
) -> Result<Vec<F::E>> {
    let mut values = Vec::with_capacity(count);
    let mut subfield = false;
    let mut first = true;
    while values.len() < count {
        let length = super::util::read_size_4bytes(bytes)?;
        if (length == 0 && !first) || length > count - values.len() {
            return Err(invalid("invalid Polygero row run length"));
        }
        first = false;
        let width = if subfield {
            sf.serialized_size_bytes()
        } else {
            f.serialized_size_bytes()
        };
        if length > bytes.len() / width {
            return Err(Error::new(ErrorKind::UnexpectedEof, "Polygero row run"));
        }
        for _ in 0..length {
            let value = if subfield {
                super::util::read_subfield_elt(bytes, sf)?
            } else {
                read_field(bytes, f)?
            };
            if sf.contains(&value) != subfield {
                return Err(invalid("noncanonical Polygero row encoding"));
            }
            values.push(value);
        }
        subfield = !subfield;
    }
    Ok(values)
}

/// Full-width responses may themselves lie in the subfield. Their encoding is
/// fixed by the response layout, independent of the row compression scheme.
fn read_field<F: SerializableField>(bytes: &mut &[u8], field: &F) -> Result<F::E> {
    let width = field.serialized_size_bytes();
    let raw = bytes
        .get(..width)
        .ok_or_else(|| Error::new(ErrorKind::UnexpectedEof, "Polygero field element"))?;
    let value = field
        .bytes_to_element(raw)
        .map_err(|_| invalid("invalid field element"))?;
    if field.to_bytes(&value) != raw {
        return Err(invalid("noncanonical field element"));
    }
    *bytes = &bytes[width..];
    Ok(value)
}

fn read_opening(bytes: &mut &[u8], geom: &PolygeroGeometry) -> Result<MerkleProof> {
    let nonce = MerkleProof::read_nonces(bytes, geom.t)?;
    let count = super::util::read_size_4bytes(bytes)?;
    if count > geom.t * (geom.n.next_power_of_two().trailing_zeros() as usize + 1)
        || count > bytes.len() / 32
    {
        return Err(invalid("Polygero frontier length"));
    }
    let path = (0..count)
        .map(|_| super::util::read_bytes_32(bytes).map(|data| Digest { data }))
        .collect::<Result<Vec<_>>>()?;
    Ok(MerkleProof { nonce, path })
}

fn validate_codecs<F: SerializableField, SF: Subfield<E = F::E>>(f: &F, sf: &SF) -> Result<()> {
    if sf.serialized_size_bytes() == 0 || sf.serialized_size_bytes() > f.serialized_size_bytes() {
        return Err(invalid("invalid Polygero subfield codec"));
    }
    Ok(())
}
