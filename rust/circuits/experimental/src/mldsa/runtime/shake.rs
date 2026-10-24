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

//! Native SHAKE and witness construction.

use super::super::shake_layout::*;
use crate::circuits::experimental::sha3::{self, ConcreteDerived};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConcreteShake256Witness {
    pub permutations: Vec<ConcreteDerived>,
}

fn permute_native(state: &mut [[u64; 5]; 5], witness: &mut ConcreteShake256Witness) {
    let trajectory = sha3::keccak_f_1600_trajectory(*state);
    witness.permutations.push(ConcreteDerived {
        intermediate_states: (0..KECCAK_ROUNDS)
            .filter(|&round| STATE_ROUNDS.contains(&round))
            .map(|round| trajectory[round + 1])
            .collect(),
    });
    *state = trajectory[24];
}

fn xof_witness(input: &[u8], output_len: usize, rate: usize) -> (Vec<u8>, ConcreteShake256Witness) {
    let mut padded = input.to_vec();
    let padding = rate - input.len() % rate;
    if padding == 1 {
        padded.push(0x9f);
    } else {
        padded.push(0x1f);
        padded.resize(padded.len() + padding - 2, 0);
        padded.push(0x80);
    }

    let mut state = [[0u64; 5]; 5];
    let mut witness = ConcreteShake256Witness {
        permutations: Vec::with_capacity(
            input.len() / rate + 1 + output_len.div_ceil(rate).saturating_sub(1),
        ),
    };
    for block in padded.chunks_exact(rate) {
        for (i, &byte) in block.iter().enumerate() {
            let lane = i / 8;
            state[lane % 5][lane / 5] ^= u64::from(byte) << (8 * (i % 8));
        }
        permute_native(&mut state, &mut witness);
    }

    let mut output = Vec::with_capacity(output_len);
    while output.len() < output_len {
        for i in 0..rate.min(output_len - output.len()) {
            let lane = i / 8;
            output.push((state[lane % 5][lane / 5] >> (8 * (i % 8))) as u8);
        }
        if output.len() < output_len {
            permute_native(&mut state, &mut witness);
        }
    }
    (output, witness)
}

pub fn shake256_witness(input: &[u8], output_len: usize) -> (Vec<u8>, ConcreteShake256Witness) {
    xof_witness(input, output_len, SHAKE256_RATE)
}

#[must_use]
pub fn shake128(input: &[u8], output_len: usize) -> Vec<u8> {
    xof_witness(input, output_len, 168).0
}

impl ConcreteShake256Witness {
    pub fn push_wires<const W: usize, F: crate::runtime::algebra::RuntimeField<W>>(
        &self,
        field: &F,
        destination: &mut Vec<F::E>,
    ) {
        for permutation in &self.permutations {
            for state in &permutation.intermediate_states {
                for row in state {
                    for &lane in row {
                        for bit in 0..64 {
                            destination.push(if (lane >> bit) & 1 == 0 {
                                field.one()
                            } else {
                                field.mone()
                            });
                        }
                    }
                }
            }
        }
    }
}
