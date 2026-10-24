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

//! Dense monomial weights for evaluating multilinear coefficient arrays.
//!
//! For coefficients v[i] and a point u, P(u) = sum_i m[i]*v[i], where
//! m[i] = product_j u[j]^i_j and i_j is bit j of i. These weights give the same
//! evaluation as binding the low variable repeatedly in `dense::bind`.
use crate::runtime::algebra::RuntimeField;

/// Return m[i] = product_j point[j]^i_j, where i_j is bit j of i.
/// point[j] corresponds to bit j, least-significant bit first. Only the first
/// logn coordinates are used. Coefficients at indices n..2^logn are implicitly
/// zero, so return only the first n weights. An empty coefficient array needs
/// no weights; the empty product for index zero has weight one.
pub(super) fn weights<const W: usize, F: RuntimeField<W>>(
    logn: usize,
    n: usize,
    point: &[F::E],
    f: &F,
) -> Vec<F::E> {
    assert!(crate::runtime::sumcheck_v2::sane_logw(logn) && point.len() >= logn);
    assert!(n as u64 <= (1u64 << logn));
    let mut weights = vec![f.zero(); n];
    if n != 0 {
        fill(&mut weights, &point[..logn], &f.one(), f);
    }
    weights
}

/// Fill a prefix of the monomial table with an accumulated high-bit weight.
/// Split on the highest remaining bit so each branch occupies a contiguous
/// block: bit 0 keeps the weight, while bit 1 multiplies it by that coordinate.
fn fill<const W: usize, F: RuntimeField<W>>(
    weights: &mut [F::E],
    point: &[F::E],
    weight: &F::E,
    f: &F,
) {
    if let Some((z, point_lo)) = point.split_last() {
        let stride = 1usize << point_lo.len();
        if stride < weights.len() {
            let weight1 = f.mulf(weight, z);
            let (weights0, weights1) = weights.split_at_mut(stride);
            fill(weights0, point_lo, weight, f);
            fill(weights1, point_lo, &weight1, f);
        } else {
            fill(weights, point_lo, weight, f);
        }
    } else {
        weights[0] = weight.clone();
    }
}
