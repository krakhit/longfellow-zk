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

use crate::{
    core::algebra::{AlgebraicField, SerializableField},
    runtime::{
        algebra::{
            gf2_128::{Gf2_128, Gf2_128Field},
            subfield::BinarySubfield,
            Subfield,
        },
        proto::{
            polygero::{self, PolygeroGeometry, PolygeroProof},
            MerkleNonce, MerkleProof,
        },
    },
};

fn geometry() -> PolygeroGeometry {
    PolygeroGeometry {
        nw: 6,
        nq: 0,
        k: 4,
        s: 1,
        n: 16,
        t: 1,
    }
}

fn proof(rows: Vec<Gf2_128>) -> PolygeroProof<Gf2_128> {
    let [h, z] = geometry()
        .response_lengths()
        .map(|n| vec![Gf2_128::from(0u128); n]);
    PolygeroProof {
        h,
        z,
        rows,
        opening: MerkleProof {
            nonce: vec![MerkleNonce { bytes: [0x57; 32] }],
            path: vec![],
        },
    }
}

fn row_offset() -> usize {
    28 + geometry().response_lengths().iter().sum::<usize>() * 16
}

#[test]
fn mixed_row_runs_have_a_self_describing_encoding() {
    let field = Gf2_128Field::new();
    let subfield = BinarySubfield::new(&crate::core::algebra::proto::GF2_16_BASIS_V1);
    let outside = Gf2_128::from(1u128 << 127);
    assert!(!subfield.contains(&outside));
    let another = field.addf(&outside, &field.one());
    // Membership varies even among the three dedicated mask-row positions.
    let sample = proof(vec![
        outside,
        field.zero(),
        field.one(),
        another,
        subfield.embed(2),
    ]);
    let bytes = sample.write(&geometry(), &field, &subfield).unwrap();
    let mut expected = Vec::new();
    expected.extend(1u32.to_le_bytes());
    expected.extend(field.to_bytes(&outside));
    expected.extend(2u32.to_le_bytes());
    expected.extend(subfield.to_bytes(&field.zero()));
    expected.extend(subfield.to_bytes(&field.one()));
    expected.extend(1u32.to_le_bytes());
    expected.extend(field.to_bytes(&another));
    expected.extend(1u32.to_le_bytes());
    expected.extend(subfield.to_bytes(&subfield.embed(2)));
    assert_eq!(&bytes[row_offset()..bytes.len() - 36], expected);
    let mut concatenated = bytes.clone();
    concatenated.extend(&bytes);
    let mut input = concatenated.as_slice();
    assert_eq!(
        polygero::read(&mut input, &geometry(), &field, &subfield).unwrap(),
        sample
    );
    assert_eq!(input, bytes);
    assert_eq!(
        polygero::read(&mut input, &geometry(), &field, &subfield).unwrap(),
        sample
    );
    assert!(input.is_empty());
}

#[test]
fn selected_columns_stay_packed_by_row_on_the_wire() {
    let field = Gf2_128Field::new();
    let subfield = BinarySubfield::new(&crate::core::algebra::proto::GF2_16_BASIS_V1);
    let geom = PolygeroGeometry {
        nw: 2,
        t: 2,
        ..geometry()
    };
    assert_eq!(geom.nrow(), 4);
    let outside = Gf2_128::from(1u128 << 127);
    let another = field.addf(&outside, &field.one());
    let sample = PolygeroProof {
        h: vec![field.zero(); geom.k + geom.s],
        z: vec![field.zero(); 2 * geom.k],
        // Two queries for each of four rows, with alternating field membership.
        rows: vec![
            outside,
            another,
            field.zero(),
            field.one(),
            outside,
            another,
            subfield.embed(2),
            subfield.embed(3),
        ],
        opening: MerkleProof {
            nonce: vec![MerkleNonce { bytes: [0x57; 32] }; geom.t],
            path: vec![],
        },
    };
    let bytes = sample.write(&geom, &field, &subfield).unwrap();
    assert_eq!(&bytes[..4], b"PLG7");
    let mut expected = Vec::new();
    expected.extend(2u32.to_le_bytes());
    expected.extend(field.to_bytes(&outside));
    expected.extend(field.to_bytes(&another));
    expected.extend(2u32.to_le_bytes());
    expected.extend(subfield.to_bytes(&field.zero()));
    expected.extend(subfield.to_bytes(&field.one()));
    expected.extend(2u32.to_le_bytes());
    expected.extend(field.to_bytes(&outside));
    expected.extend(field.to_bytes(&another));
    expected.extend(2u32.to_le_bytes());
    expected.extend(subfield.to_bytes(&subfield.embed(2)));
    expected.extend(subfield.to_bytes(&subfield.embed(3)));
    assert_eq!(
        &bytes[row_offset()..bytes.len() - 32 * geom.t - 4],
        expected
    );
    let mut input = bytes.as_slice();
    assert_eq!(
        polygero::read(&mut input, &geom, &field, &subfield).unwrap(),
        sample
    );
    assert!(input.is_empty());
    let mut incomplete = sample;
    incomplete.rows.pop();
    assert!(incomplete.write(&geom, &field, &subfield).is_err());
}

#[test]
fn virtual_product_rows_are_absent_from_the_wire() {
    let field = Gf2_128Field::new();
    let subfield = BinarySubfield::new(&crate::core::algebra::proto::GF2_16_BASIS_V1);
    let geom = PolygeroGeometry {
        nw: 3,
        nq: 3,
        k: 8,
        t: 2,
        ..geometry()
    };
    // Three masks, one ordinary row, and two product groups. Only each group's
    // x,y pair is sent, so the ten committed rows require eight proof rows.
    assert_eq!(geom.nrow(), 10);
    assert_eq!(geom.transmitted_rows(), 8);
    let sample = PolygeroProof {
        h: vec![field.zero(); geom.k + geom.s],
        z: vec![field.zero(); 2 * geom.k],
        rows: (0..16).map(|i| subfield.embed(i)).collect(),
        opening: MerkleProof {
            nonce: vec![MerkleNonce { bytes: [0x57; 32] }; geom.t],
            path: vec![],
        },
    };
    let bytes = sample.write(&geom, &field, &subfield).unwrap();
    let rows_offset = 28 + (sample.h.len() + sample.z.len()) * field.serialized_size_bytes();
    let mut expected = Vec::new();
    expected.extend(0u32.to_le_bytes());
    expected.extend(16u32.to_le_bytes());
    for value in &sample.rows {
        expected.extend(subfield.to_bytes(value));
    }
    assert_eq!(&bytes[rows_offset..bytes.len() - 32 * geom.t - 4], expected,);
    let mut input = bytes.as_slice();
    assert_eq!(
        polygero::read(&mut input, &geom, &field, &subfield).unwrap(),
        sample,
    );
    assert!(input.is_empty());

    // Supplying the two virtual rows is a shape error, not an alternate encoding.
    let mut full = sample;
    full.rows.extend(vec![field.zero(); 2 * geom.t]);
    assert!(full.write(&geom, &field, &subfield).is_err());
}

#[test]
fn every_row_membership_pattern_roundtrips_canonically() {
    let field = Gf2_128Field::new();
    let subfield = BinarySubfield::new(&crate::core::algebra::proto::GF2_16_BASIS_V1);
    let outside = Gf2_128::from(1u128 << 127);
    for pattern in 0..32 {
        let sample = proof(
            (0..5)
                .map(|i| {
                    if pattern & (1 << i) != 0 {
                        subfield.embed(i)
                    } else {
                        outside
                    }
                })
                .collect(),
        );
        let bytes = sample.write(&geometry(), &field, &subfield).unwrap();
        let mut input = bytes.as_slice();
        let decoded = polygero::read(&mut input, &geometry(), &field, &subfield).unwrap();
        assert!(input.is_empty());
        assert_eq!(decoded, sample);
        assert_eq!(
            decoded.write(&geometry(), &field, &subfield).unwrap(),
            bytes
        );
    }
}

#[test]
fn malformed_row_runs_are_rejected() {
    let field = Gf2_128Field::new();
    let subfield = BinarySubfield::new(&crate::core::algebra::proto::GF2_16_BASIS_V1);
    let outside = Gf2_128::from(1u128 << 127);
    let bytes = proof(vec![outside; 5])
        .write(&geometry(), &field, &subfield)
        .unwrap();
    let offset = row_offset();
    for length in [6u32, u32::MAX] {
        let mut oversized = bytes.clone();
        oversized[offset..offset + 4].copy_from_slice(&length.to_le_bytes());
        assert!(polygero::read(&mut oversized.as_slice(), &geometry(), &field, &subfield).is_err());
    }
    let mut empty_runs = bytes.clone();
    empty_runs.splice(offset..offset, [0u8; 8]);
    assert!(polygero::read(&mut empty_runs.as_slice(), &geometry(), &field, &subfield).is_err());
    let mut wrong_class = bytes.clone();
    wrong_class[offset + 4..offset + 20].copy_from_slice(&field.to_bytes(&field.zero()));
    assert!(polygero::read(&mut wrong_class.as_slice(), &geometry(), &field, &subfield).is_err());
    let mixed = proof(vec![outside, field.zero(), outside, outside, outside]);
    let mut empty_middle = mixed.write(&geometry(), &field, &subfield).unwrap();
    empty_middle[offset + 20..offset + 24].fill(0);
    assert!(polygero::read(&mut empty_middle.as_slice(), &geometry(), &field, &subfield).is_err());
    for length in 0..bytes.len() {
        assert!(polygero::read(&mut &bytes[..length], &geometry(), &field, &subfield).is_err());
    }
    for marker in [b"PYG2", b"PYG3", b"PYG4", b"PYG5", b"PYG6", b"PYG7"] {
        let mut old_version = bytes.clone();
        old_version[..4].copy_from_slice(marker);
        assert!(
            polygero::read(&mut old_version.as_slice(), &geometry(), &field, &subfield).is_err()
        );
    }
}

struct AliasedZero;
impl Subfield for AliasedZero {
    type E = Gf2_128;
    fn contains(&self, value: &Self::E) -> bool {
        *value == Gf2_128::from(0u128)
    }
    fn serialized_size_bytes(&self) -> usize {
        1
    }
    fn to_bytes_into(&self, _: &Self::E, out: &mut [u8]) {
        out[0] = 0;
    }
    fn bytes_to_element(&self, _: &[u8]) -> Result<Self::E, String> {
        Ok(Gf2_128::from(0u128))
    }
    fn sample<R: FnMut(usize) -> Vec<u8>>(&self, _: R) -> Self::E {
        Gf2_128::from(0u128)
    }
}

#[test]
fn noncanonical_subfield_bytes_are_rejected() {
    let field = Gf2_128Field::new();
    let sample = proof(vec![field.zero(); 5]);
    let mut bytes = sample.write(&geometry(), &field, &AliasedZero).unwrap();
    assert_eq!(
        polygero::read(&mut bytes.as_slice(), &geometry(), &field, &AliasedZero).unwrap(),
        sample
    );
    // Empty full-field run, then five compact values. Alias 1 decodes as zero
    // but must be rejected because zero's unique compact representation is 0.
    bytes[row_offset() + 8] = 1;
    assert!(polygero::read(&mut bytes.as_slice(), &geometry(), &field, &AliasedZero).is_err());
}
