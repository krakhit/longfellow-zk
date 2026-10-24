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

//! Native SampleInBall and its witness.

use super::{
    super::params::{MlDsaParams, N},
    shake::{shake256_witness, ConcreteShake256Witness},
    Polynomial,
};
use crate::core::algebra::fp24::Q;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConcreteSampleInBallWitness {
    pub shake: ConcreteShake256Witness,
    pub samples: Vec<u8>,
    pub sample_indices: Vec<u16>,
    pub position_trace: Vec<Vec<u8>>,
}

pub fn sample_in_ball<P: MlDsaParams>(
    seed: &[u8],
) -> Option<(Polynomial, ConcreteSampleInBallWitness)> {
    if seed.len() != P::C_TILDE_BYTES {
        return None;
    }
    let (hash, shake) = shake256_witness(seed, 136);
    let mut coefficients = [0u32; N];
    let mut samples = Vec::with_capacity(P::TAU);
    let mut sample_indices = Vec::with_capacity(P::TAU);
    let mut hash_index = 8;
    for i in N - P::TAU..N {
        let sample = loop {
            let value = *hash.get(hash_index)?;
            let index = hash_index;
            hash_index += 1;
            if usize::from(value) <= i {
                sample_indices.push(index as u16);
                break value;
            }
        };
        samples.push(sample);
        coefficients[i] = coefficients[usize::from(sample)];
        coefficients[usize::from(sample)] =
            if (hash[(i + P::TAU - N) / 8] >> ((i + P::TAU - N) % 8)) & 1 == 1 {
                Q - 1
            } else {
                1
            };
    }

    let mut current_positions = Vec::with_capacity(P::TAU);
    let mut position_trace = Vec::with_capacity(P::TAU);
    for (step, &sample) in samples.iter().enumerate() {
        if let Some(position) = current_positions
            .iter_mut()
            .find(|position| **position == sample)
        {
            *position = (N - P::TAU + step) as u8;
        }
        current_positions.push(sample);
        position_trace.push(current_positions.clone());
    }
    Some((
        coefficients,
        ConcreteSampleInBallWitness {
            shake,
            samples,
            sample_indices,
            position_trace,
        },
    ))
}

impl ConcreteSampleInBallWitness {
    pub fn push_wires<const W: usize, F: crate::runtime::algebra::RuntimeField<W>>(
        &self,
        field: &F,
        destination: &mut Vec<F::E>,
    ) {
        for (&sample, &index) in self.samples.iter().zip(&self.sample_indices) {
            super::push_bitvec_u64(field, u64::from(sample), 8, destination);
            super::push_bitvec_u64(field, u64::from(index), 16, destination);
        }
        self.shake.push_wires(field, destination);
        for trace in &self.position_trace {
            for &position in trace {
                super::push_bitvec_u64(field, u64::from(position), 8, destination);
            }
        }
    }
}
