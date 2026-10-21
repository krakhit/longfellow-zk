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

pub mod dense;
pub mod eq;
pub mod eval;
pub mod hquad;
pub mod pad;
pub mod poly;
pub mod transcript;

pub use dense::{as_scalar, bind, bind_all, normalize};
pub use eq::eval as eq;
pub use hquad::HQuad;
pub use poly::{LagrangeBasis, Poly, QuadRoundPoly, QuadWirePoly};
pub use proof::{sane_logw, LayerProof, RoundPoly, SumcheckProof, MAX_LOGW};
pub use transcript::TranscriptSumcheck;

pub use crate::runtime::{
    proto::sumcheck as proof,
    random::{RandomEngine, Transcript},
    sumcheck::eval::{eval_circuit, eval_quad},
};

pub struct SumcheckProofAux<const W: usize, F: crate::runtime::algebra::poly::InterpolationField<W>>
{
    pub bound_quad: Vec<crate::core::algebra::ElementOf<F>>,
}

cfg_prover! {
    pub mod prover;
    pub use prover::{prove, prove_core};
}

cfg_verifier! {
    pub mod verifier;
    pub use verifier::{verify, Claims};
}

#[cfg(test)]
#[path = "../tests/all/mod.rs"]
mod tests_all;
