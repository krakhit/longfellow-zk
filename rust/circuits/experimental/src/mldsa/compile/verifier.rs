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

//! Integrated ML-DSA verifier circuit and native witness generation.

use crate::circuits::bitvec::{BitvecIO, BitvecLogic, V8};
use crate::circuits::boolean::{Bitw, BooleanIO};
use crate::compile::logic::{Logic, LogicIO};
use crate::core::algebra::SupportsU64Conversions;

use super::{
    super::params::{MlDsaParams, N},
    circuit::{MlDsaCircuit, PolynomialW},
    sample::{
        allocate_witness as allocate_sample_witness, assert_sample_in_ball, SampleInBallWitness,
    },
    shake::{allocate_witness as allocate_shake_witness, Shake256, Shake256Witness},
};
use std::marker::PhantomData;

pub type BitDecompositions<L> = Vec<Vec<Vec<Bitw<L>>>>;

fn input_bytes<L: LogicIO>(bitvec: &BitvecLogic<L>, position: &mut usize, n: usize) -> Vec<V8<L>> {
    let io = BitvecIO::new(bitvec);
    (0..n).map(|_| io.next(position)).collect()
}

fn input_bits<L: LogicIO>(logic: &L, position: &mut usize, n: usize) -> Vec<Bitw<L>> {
    let io = BooleanIO::new(logic);
    (0..n).map(|_| io.next(position)).collect()
}

fn input_polynomials<L: LogicIO>(logic: &L, position: &mut usize, n: usize) -> Vec<PolynomialW<L>> {
    (0..n)
        .map(|_| PolynomialW::input(logic, position))
        .collect()
}

fn input_decompositions<L: LogicIO>(
    logic: &L,
    position: &mut usize,
    polynomials: usize,
    width: usize,
) -> BitDecompositions<L> {
    (0..polynomials)
        .map(|_| (0..N).map(|_| input_bits(logic, position, width)).collect())
        .collect()
}

pub struct PublicKeyW<L: Logic> {
    pub a_hat: Vec<Vec<PolynomialW<L>>>,
    pub ntt_t1: Vec<PolynomialW<L>>,
}

impl<L: LogicIO> PublicKeyW<L> {
    pub fn input<P: MlDsaParams>(logic: &L, bitvec: &BitvecLogic<L>, position: &mut usize) -> Self {
        let a_hat = (0..P::K)
            .map(|_| input_polynomials(logic, position, P::L))
            .collect();
        let ntt_t1 = input_polynomials(logic, position, P::K);
        let _ = bitvec;
        Self { a_hat, ntt_t1 }
    }
}

pub struct SignatureW<L: Logic> {
    pub c_tilde: Vec<V8<L>>,
    pub z: Vec<PolynomialW<L>>,
    pub z_bits: BitDecompositions<L>,
    pub h: Vec<PolynomialW<L>>,
}

impl<L: LogicIO> SignatureW<L> {
    pub fn input<P: MlDsaParams>(logic: &L, bitvec: &BitvecLogic<L>, position: &mut usize) -> Self {
        Self {
            c_tilde: input_bytes(bitvec, position, P::C_TILDE_BYTES),
            z: input_polynomials(logic, position, P::L),
            z_bits: input_decompositions(logic, position, P::L, P::Z_BITS),
            h: input_polynomials(logic, position, P::K),
        }
    }
}

pub struct VerificationWitness<L: Logic> {
    pub sample: SampleInBallWitness<L>,
    pub c: PolynomialW<L>,
    pub approximation: Vec<PolynomialW<L>>,
    pub raw_high: Vec<PolynomialW<L>>,
    pub raw_high_bits: BitDecompositions<L>,
    pub hint_auxiliary_bits: BitDecompositions<L>,
    pub hinted_high: Vec<PolynomialW<L>>,
    pub hinted_high_bits: BitDecompositions<L>,
    pub ntt_z: Vec<PolynomialW<L>>,
    pub ntt_c: PolynomialW<L>,
    pub encoded_w1: Vec<V8<L>>,
    pub challenge_hash: Shake256Witness<L>,
    pub hint_sum_bits: Vec<Bitw<L>>,
}

impl<L: LogicIO> VerificationWitness<L> {
    pub fn input<P: MlDsaParams>(logic: &L, bitvec: &BitvecLogic<L>, position: &mut usize) -> Self {
        let sample = allocate_sample_witness::<_, P>(bitvec, position);
        let c = PolynomialW::input(logic, position);
        let mut approximation = Vec::with_capacity(P::K);
        let mut raw_high = Vec::with_capacity(P::K);
        let mut raw_high_bits = Vec::with_capacity(P::K);
        let mut hint_auxiliary_bits = Vec::with_capacity(P::K);
        let mut hinted_high = Vec::with_capacity(P::K);
        let mut hinted_high_bits = Vec::with_capacity(P::K);
        for _ in 0..P::K {
            approximation.push(PolynomialW::input(logic, position));
            raw_high.push(PolynomialW::input(logic, position));
            raw_high_bits.push(
                (0..N)
                    .map(|_| input_bits(logic, position, P::R1_BITS))
                    .collect(),
            );
            hint_auxiliary_bits.push(
                (0..N)
                    .map(|_| input_bits(logic, position, P::r0_bits() + 1))
                    .collect(),
            );
            hinted_high.push(PolynomialW::input(logic, position));
            hinted_high_bits.push(
                (0..N)
                    .map(|_| input_bits(logic, position, P::R1_BITS))
                    .collect(),
            );
        }
        let ntt_z = input_polynomials(logic, position, P::L);
        let ntt_c = PolynomialW::input(logic, position);
        let encoded_w1 = input_bytes(bitvec, position, P::K * P::W1_BYTES);
        let challenge_hash =
            allocate_shake_witness(bitvec, position, 64 + P::K * P::W1_BYTES, P::C_TILDE_BYTES);
        let hint_sum_bits = input_bits(
            logic,
            position,
            (usize::BITS - P::OMEGA.leading_zeros()) as usize,
        );
        Self {
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
            hint_sum_bits,
        }
    }
}

pub struct MlDsaVerifier<'a, L: Logic, P: MlDsaParams> {
    logic: &'a L,
    bitvec: BitvecLogic<'a, L>,
    arithmetic: MlDsaCircuit<'a, L, P>,
    _params: PhantomData<P>,
}

impl<'a, L, P> MlDsaVerifier<'a, L, P>
where
    L: Logic,
    L::F: SupportsU64Conversions,
    P: MlDsaParams,
{
    pub fn new(logic: &'a L) -> Self {
        Self {
            logic,
            bitvec: BitvecLogic::new(logic),
            arithmetic: MlDsaCircuit::new(logic),
            _params: PhantomData,
        }
    }

    /// Checks the signature against an expanded public key and a supplied 64-byte mu.
    /// Key expansion and message-to-mu hashing are performed outside this circuit;
    /// the caller is responsible for binding these inputs to its intended statement.
    pub fn assert_valid_signature_on_mu(
        &self,
        public_key: &PublicKeyW<L>,
        signature: &SignatureW<L>,
        mu: &[V8<L>],
        witness: &VerificationWitness<L>,
    ) -> L::Assertions {
        assert_eq!(mu.len(), 64);
        let sample = assert_sample_in_ball::<_, P>(
            self.logic,
            &signature.c_tilde,
            &witness.c,
            &witness.sample,
        );
        let approximation = self.arithmetic.assert_w_approximation(
            &public_key.a_hat,
            &public_key.ntt_t1,
            &signature.z,
            &witness.c,
            &witness.ntt_z,
            &witness.ntt_c,
            &witness.approximation,
        );
        let hints = self.arithmetic.assert_use_hint(
            &signature.h,
            &witness.approximation,
            &witness.raw_high,
            &witness.raw_high_bits,
            &witness.hint_auxiliary_bits,
            &witness.hinted_high,
            &witness.hinted_high_bits,
            &witness.hint_sum_bits,
        );
        let encoding = self
            .arithmetic
            .assert_w1_encode(&witness.hinted_high_bits, &witness.encoded_w1);
        let norm = self.arithmetic.assert_infinity_norm(
            "z_norm",
            &signature.z,
            &signature.z_bits,
            P::Z_BITS,
            P::GAMMA1 - P::REJECTION_BOUND,
        );

        let mut hash_input = mu.to_vec();
        hash_input.extend(witness.encoded_w1.iter().cloned());
        let shake = Shake256::new(self.logic);
        let (computed_challenge, hash_assertions) =
            shake.assert_hash(&hash_input, P::C_TILDE_BYTES, &witness.challenge_hash);
        let challenge_equality =
            self.logic
                .assert_mapi("challenge_hash", 0..P::C_TILDE_BYTES, |i| {
                    self.bitvec
                        .assert_eq("byte", &computed_challenge[i], &signature.c_tilde[i])
                });
        self.logic.assert_all(
            "mldsa_verify",
            &[
                sample,
                approximation,
                hints,
                encoding,
                norm,
                hash_assertions,
                challenge_equality,
            ],
        )
    }
}
