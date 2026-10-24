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

//! Native ML-DSA arithmetic and witness generation; independent of the compiler.

/// A native polynomial in the MLDSA negacyclic ring.
pub type Polynomial = [u32; super::params::N];

pub mod reference;
pub mod sample;
pub mod shake;
pub mod verifier;

fn push_bitvec_u64<const W: usize, F: crate::runtime::algebra::RuntimeField<W>>(
    field: &F,
    value: u64,
    width: usize,
    destination: &mut Vec<F::E>,
) {
    assert!(width <= 64);
    destination.extend((0..width).map(|i| {
        if value >> i & 1 == 0 {
            field.zero()
        } else {
            field.one()
        }
    }));
}
