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

//! Form dense coefficient arrays by binding a sparse circuit tensor.
//!
//! In QUAD[g,l,r], g indexes layer outputs and l,r index its input wires.
//! Both routines bind g with the weights a[g]. `bind_l` also binds l with b_l[l],
//! leaving q_r[r]; `bind_r` binds r with b_r[r], leaving q_l[l]. The protocol uses
//! b_l = m_l, the monomial weights at the sampled point, and b_r = W, the witness.
//!
//! A zero coefficient marks an assertion quad. Its sampled assertion coefficient
//! replaces the entire a[g]*QUAD[g,l,r] factor. Both bindings consume the same
//! assertion sequence in circuit traversal order.
use crate::{
    core::proto::{Layer, SerializableField},
    runtime::{
        algebra::{blas, RuntimeField},
        sumcheck_v2::monomial,
    },
};

/// Bind g,l with a,b_l, leaving r free:
/// `q_r[r] = sum_{g,l} a[g] QUAD[g,l,r] b_l[l]`.
/// Both parties use b_l[l] = m_l[l] = product_j u[j]^l_j at the sampled point u.
pub(super) fn bind_l<const W: usize, F: RuntimeField<W> + SerializableField>(
    layer: &Layer<F>,
    constants: &[F::E],
    a: &[F::E],
    assertions: &[F::E],
    b_l: &[F::E],
    f: &F,
) -> Vec<F::E> {
    let mut q_r = vec![f.zero(); layer.nw()];
    let one = f.one();
    let mut assertion_challenges = assertions.iter();
    layer.for_each_term(constants, |term| {
        let g = term.g as usize;
        let coefficient = if f.is_zero(&term.k) {
            assertion_challenges
                .next()
                .expect("missing assertion challenge")
                .clone()
        } else if term.k == one {
            a[g].clone()
        } else {
            f.mulf(&a[g], &term.k)
        };
        let l = term.h0 as usize;
        let r = term.h1 as usize;
        f.fma(&mut q_r[r], &coefficient, &b_l[l]);
    });
    assert!(
        assertion_challenges.next().is_none(),
        "unused assertion challenge"
    );
    q_r
}

/// Bind g,r with a,b_r, leaving l free:
/// `q_l[l] = sum_{g,r} a[g] QUAD[g,l,r] b_r[r]`.
/// The prover uses b_r[r] = W[r], the layer's input witness.
#[cfg(any(test, feature = "prover"))]
pub(super) fn bind_r<const W: usize, F: RuntimeField<W> + SerializableField>(
    layer: &Layer<F>,
    constants: &[F::E],
    a: &[F::E],
    assertions: &[F::E],
    b_r: &[F::E],
    f: &F,
) -> Vec<F::E> {
    let mut q_l = vec![f.zero(); layer.nw()];
    let one = f.one();
    let mut assertion_challenges = assertions.iter();
    layer.for_each_term(constants, |term| {
        let g = term.g as usize;
        let coefficient = if f.is_zero(&term.k) {
            // Replace each assertion marker's zero coefficient by its own
            // challenge, in quad order. Both bindings reuse this sequence.
            assertion_challenges
                .next()
                .expect("missing assertion challenge")
                .clone()
        } else if term.k == one {
            a[g].clone()
        } else {
            f.mulf(&a[g], &term.k)
        };
        let l = term.h0 as usize;
        let r = term.h1 as usize;
        f.fma(&mut q_l[l], &coefficient, &b_r[r]);
    });
    assert!(
        assertion_challenges.next().is_none(),
        "unused assertion challenge"
    );
    q_l
}

/// Express A + alpha*B as weights on the layer's input wires:
///
/// ```text
/// m_l[l] = product_j point_l[j]^l_j,
/// q_r[r] = sum_{g,l} a[g] QUAD[g,l,r] m_l[l],
/// a_next[r] = m_l[r] + alpha*q_r[r].
/// ```
///
/// Thus sum_r a_next[r]*W[r] = A + alpha*B. Prover and verifier use the same
/// public computation; only bind_r, above, needs the prover's witness.
pub(super) fn weights_next<const W: usize, F: RuntimeField<W> + SerializableField>(
    layer: &Layer<F>,
    constants: &[F::E],
    a: &[F::E],
    assertions: &[F::E],
    point_l: &[F::E],
    alpha: &F::E,
    f: &F,
) -> Vec<F::E> {
    let mut a_next = monomial::weights(layer.logw(), layer.nw(), point_l, f);
    let q_r = bind_l(layer, constants, a, assertions, &a_next, f);
    blas::axpy(&mut a_next, alpha, &q_r, f);
    a_next
}
