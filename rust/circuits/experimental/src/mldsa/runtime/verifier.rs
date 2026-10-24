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

//! Native ML-DSA instances and ordered prover witnesses.

use super::{
    super::params::{MlDsaParams, N},
    reference::{
        decode_public_key, decode_signature, decompose, encode_w1, inverse_ntt, ntt,
        preprocess_message, use_hint, Polynomial, Signature,
    },
    sample::{sample_in_ball, ConcreteSampleInBallWitness},
    shake::{shake256_witness, ConcreteShake256Witness},
};
use crate::core::algebra::{
    fp24::{add_base as q_add, mul_base as q_mul, sub_base as q_sub, Q},
    SupportsU64Conversions,
};
use std::marker::PhantomData;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConcretePublicKey {
    pub a_hat: Vec<Vec<Polynomial>>,
    pub ntt_t1: Vec<Polynomial>,
    pub tr: [u8; 64],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConcreteSignature {
    pub c_tilde: Vec<u8>,
    pub z: Vec<Polynomial>,
    pub z_bits: Vec<Vec<u64>>,
    pub h: Vec<Polynomial>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConcreteVerificationWitness {
    pub sample: ConcreteSampleInBallWitness,
    pub c: Polynomial,
    pub approximation: Vec<Polynomial>,
    pub raw_high: Vec<Polynomial>,
    pub raw_high_bits: Vec<Vec<u64>>,
    pub hint_auxiliary_bits: Vec<Vec<u64>>,
    pub hinted_high: Vec<Polynomial>,
    pub hinted_high_bits: Vec<Vec<u64>>,
    pub ntt_z: Vec<Polynomial>,
    pub ntt_c: Polynomial,
    pub encoded_w1: Vec<u8>,
    pub challenge_hash: ConcreteShake256Witness,
    pub hint_sum: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConcreteInstance<P: MlDsaParams> {
    pub public_key: ConcretePublicKey,
    pub signature: ConcreteSignature,
    pub witness: ConcreteVerificationWitness,
    pub mu: [u8; 64],
    _params: PhantomData<P>,
}

fn make_signature<P: MlDsaParams>(signature: &Signature) -> ConcreteSignature {
    let bound = P::GAMMA1 - P::REJECTION_BOUND;
    let z_bits = signature
        .z
        .iter()
        .map(|polynomial| {
            polynomial
                .iter()
                .map(|&coefficient| {
                    let signed = if coefficient > Q / 2 {
                        i64::from(coefficient) - i64::from(Q)
                    } else {
                        i64::from(coefficient)
                    };
                    (signed + i64::from(bound - 1)) as u64
                })
                .collect()
        })
        .collect();
    let h = signature
        .h
        .iter()
        .map(|polynomial| polynomial.map(u32::from))
        .collect();
    ConcreteSignature {
        c_tilde: signature.c_tilde.clone(),
        z: signature.z.clone(),
        z_bits,
        h,
    }
}

impl<P: MlDsaParams> ConcreteInstance<P> {
    pub fn new(
        public_key_bytes: &[u8],
        signature_bytes: &[u8],
        message: &[u8],
        context: &[u8],
    ) -> Option<Self> {
        let public_key = decode_public_key::<P>(public_key_bytes)?;
        let signature = decode_signature::<P>(signature_bytes)?;
        let ntt_t1 = public_key.ntt_t1();
        let mut mu_input = public_key.tr.to_vec();
        mu_input.extend(preprocess_message(message, context)?);
        let mu: [u8; 64] = shake256_witness(&mu_input, 64).0.try_into().unwrap();
        let (c, sample) = sample_in_ball::<P>(&signature.c_tilde)?;
        let mut ntt_c = c;
        ntt(&mut ntt_c);
        let mut ntt_z = signature.z.clone();
        for polynomial in &mut ntt_z {
            ntt(polynomial);
        }

        let mut approximation = Vec::with_capacity(P::K);
        let mut raw_high = Vec::with_capacity(P::K);
        let mut raw_high_bits = Vec::with_capacity(P::K);
        let mut hint_auxiliary_bits = Vec::with_capacity(P::K);
        let mut hinted_high = Vec::with_capacity(P::K);
        let mut hinted_high_bits = Vec::with_capacity(P::K);
        for (row, ntt_t1_row) in ntt_t1.iter().enumerate().take(P::K) {
            let mut approximate = [0u32; N];
            for (column, ntt_z_column) in ntt_z.iter().enumerate().take(P::L) {
                for i in 0..N {
                    approximate[i] = q_add(
                        approximate[i],
                        q_mul(public_key.a_hat[row][column][i], ntt_z_column[i]),
                    );
                }
            }
            for i in 0..N {
                approximate[i] = q_sub(approximate[i], q_mul(ntt_c[i], ntt_t1_row[i]));
            }
            inverse_ntt(&mut approximate);
            let mut raw = [0u32; N];
            let mut aux = Vec::with_capacity(N);
            let mut hinted = [0u32; N];
            for i in 0..N {
                let (r1, r0) = decompose::<P>(approximate[i] as i32);
                raw[i] = r1 as u32;
                hinted[i] = use_hint::<P>(signature.h[row][i], approximate[i] as i32);
                aux.push((r0 + P::GAMMA2 as i32) as u64 | (u64::from(r0 <= 0) << P::r0_bits()));
            }
            approximation.push(approximate);
            raw_high_bits.push(raw.iter().map(|&value| u64::from(value)).collect());
            hint_auxiliary_bits.push(aux);
            hinted_high_bits.push(hinted.iter().map(|&value| u64::from(value)).collect());
            raw_high.push(raw);
            hinted_high.push(hinted);
        }
        let encoded_w1 = encode_w1::<P>(&hinted_high)?;
        let mut challenge_input = mu.to_vec();
        challenge_input.extend(&encoded_w1);
        let (computed_challenge, challenge_hash) =
            shake256_witness(&challenge_input, P::C_TILDE_BYTES);
        if computed_challenge != signature.c_tilde {
            return None;
        }
        let hint_sum = signature.h.iter().flatten().filter(|&&hint| hint).count() as u64;
        Some(Self {
            public_key: ConcretePublicKey {
                a_hat: public_key.a_hat,
                ntt_t1,
                tr: public_key.tr,
            },
            signature: make_signature::<P>(&signature),
            witness: ConcreteVerificationWitness {
                sample,
                c,
                approximation,
                raw_high,
                raw_high_bits,
                hint_auxiliary_bits,
                hinted_high,
                hinted_high_bits,
                ntt_z,
                ntt_c,
                encoded_w1,
                challenge_hash,
                hint_sum,
            },
            mu,
            _params: PhantomData,
        })
    }
}

fn push_polynomial<const W: usize, F>(
    field: &F,
    polynomial: &Polynomial,
    destination: &mut Vec<F::E>,
) where
    F: crate::runtime::algebra::RuntimeField<W> + crate::core::algebra::SupportsU64Conversions,
{
    destination.extend(
        polynomial
            .iter()
            .map(|&coefficient| field.u64_to_element(u64::from(coefficient))),
    );
}

fn push_bytes<const W: usize, F: crate::runtime::algebra::RuntimeField<W>>(
    field: &F,
    bytes: &[u8],
    destination: &mut Vec<F::E>,
) {
    for &byte in bytes {
        super::push_bitvec_u64(field, u64::from(byte), 8, destination);
    }
}

fn push_bits<const W: usize, F>(field: &F, value: u64, width: usize, destination: &mut Vec<F::E>)
where
    F: crate::runtime::algebra::RuntimeField<W>,
{
    super::push_bitvec_u64(field, value, width, destination);
}

impl<P: MlDsaParams> ConcreteInstance<P> {
    pub fn push_wires<
        F: crate::runtime::algebra::RuntimeField<W> + SupportsU64Conversions,
        const W: usize,
    >(
        &self,
        field: &F,
        destination: &mut Vec<F::E>,
    ) {
        for row in &self.public_key.a_hat {
            for polynomial in row {
                push_polynomial(field, polynomial, destination);
            }
        }
        for polynomial in &self.public_key.ntt_t1 {
            push_polynomial(field, polynomial, destination);
        }
        push_bytes(field, &self.signature.c_tilde, destination);
        for polynomial in &self.signature.z {
            push_polynomial(field, polynomial, destination);
        }
        for polynomial in &self.signature.z_bits {
            for &value in polynomial {
                push_bits(field, value, P::Z_BITS, destination);
            }
        }
        for polynomial in &self.signature.h {
            push_polynomial(field, polynomial, destination);
        }

        self.witness.sample.push_wires(field, destination);
        push_polynomial(field, &self.witness.c, destination);
        for row in 0..P::K {
            push_polynomial(field, &self.witness.approximation[row], destination);
            push_polynomial(field, &self.witness.raw_high[row], destination);
            for &value in &self.witness.raw_high_bits[row] {
                push_bits(field, value, P::R1_BITS, destination);
            }
            for &value in &self.witness.hint_auxiliary_bits[row] {
                push_bits(field, value, P::r0_bits() + 1, destination);
            }
            push_polynomial(field, &self.witness.hinted_high[row], destination);
            for &value in &self.witness.hinted_high_bits[row] {
                push_bits(field, value, P::R1_BITS, destination);
            }
        }
        for polynomial in &self.witness.ntt_z {
            push_polynomial(field, polynomial, destination);
        }
        push_polynomial(field, &self.witness.ntt_c, destination);
        push_bytes(field, &self.witness.encoded_w1, destination);
        self.witness.challenge_hash.push_wires(field, destination);
        super::push_bitvec_u64(
            field,
            self.witness.hint_sum,
            (usize::BITS - P::OMEGA.leading_zeros()) as usize,
            destination,
        );
        push_bytes(field, &self.mu, destination);
    }
}
