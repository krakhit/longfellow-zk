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

//! Turn A*w + b = 0 and product-copy equalities into dense logical samples C_i.
//!
//! The same routine serves both roles. Each returned vector has k entries and
//! corresponds to one data row of W. Entry j is C_i(x_j), not a monomial
//! coefficient. Mask slots and unused witness slots have coefficient zero.
//! After interpolation, the prover uses these polynomials to form Z and the
//! verifier reconstructs their values at the opened columns.
use super::{ensure, PolygeroError, PolygeroLinearTerm, PolygeroParam};
use crate::runtime::algebra::{blas, RuntimeField};

/// Check public constraint indices before consuming transcript challenges.
pub(super) fn validate<E>(
    nw: usize,
    equations: usize,
    a: &[PolygeroLinearTerm<E>],
) -> Result<(), PolygeroError> {
    ensure(
        a.iter().all(|term| term.c < equations && term.w < nw),
        "linear constraint index out of bounds",
    )
}

/// Combine the equations A*w + b = 0 and the product-copy equalities using alpha.
/// The first b.len() scalars weight linear equations; each product then has
/// three scalars for its input and output copies. The constant contribution
/// sum_c alpha[c]*b[c] is checked separately; these rows contain only variable
/// weights. Return data rows in W order, excluding the three dedicated mask rows.
pub(super) fn batch_constraints<const W: usize, F: RuntimeField<W>>(
    param: &PolygeroParam,
    b: &[F::E],
    a: &[PolygeroLinearTerm<F::E>],
    alpha: &[F::E],
    f: &F,
) -> Vec<Vec<F::E>> {
    let g = param.geom;
    let (copy_weights, _) = alpha[b.len()..b.len() + 3 * g.nq].as_chunks::<3>();
    let mut rows = {
        let mut witness_coefficients = vec![f.zero(); g.nw];
        // Accumulate all terms at their original witness indices, including repeats.
        for term in a {
            f.fma(&mut witness_coefficients[term.w], &alpha[term.c], &term.k);
        }
        // Each equality is weight * (copy - original) = 0. The positive copy
        // coefficients are laid out below; subtract their weights at the originals.
        for i in 0..g.nq {
            let product = &param.products[i];
            let weights = &copy_weights[i];
            f.sub(&mut witness_coefficients[product.x], &weights[0]);
            f.sub(&mut witness_coefficients[product.y], &weights[1]);
            f.sub(&mut witness_coefficients[product.z], &weights[2]);
        }

        // Place ordinary coefficients after the T reserved mask slots. Unused
        // slots stay zero; row boundaries follow contiguous witness blocks.
        let mut rows = Vec::with_capacity(g.data_rows());
        for block in witness_coefficients.chunks(g.ordinary_width()) {
            let mut row = vec![f.zero(); g.k];
            blas::copy(&mut row[g.t..g.t + block.len()], block);
            rows.push(row);
        }
        rows
    };

    // Place positive copy weights in consecutive input/input/output row triples.
    // The product width is needed only when there are product constraints.
    if g.nq != 0 {
        for group in copy_weights.chunks(g.product_width()) {
            let mut triple: [Vec<F::E>; 3] = std::array::from_fn(|_| vec![f.zero(); g.k]);
            for slot in 0..group.len() {
                for part in 0..3 {
                    // This is the +weight contribution. Each slot starts at zero
                    // and has no other contributions, so assign instead of adding.
                    triple[part][g.t + slot] = group[slot][part].clone();
                }
            }
            rows.extend(triple);
        }
    }
    rows
}
