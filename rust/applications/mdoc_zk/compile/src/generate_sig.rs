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

use crate::compile::algebra::p256::P256Field;
use crate::core::algebra::SerializableField;
use crate::core::proto::circuit::Circuit;
use crate::mdoc::circuits::{
    config::K_SIG_MAC_BIT_PLUCKER, signature::circuit::MdocSignature, MdocSigCompileField,
};
use crate::runtime::algebra::SupportsFFT;

use crate::mdoc::compile::{allocate_sig::allocate_sig, allocator::WireAllocator};

pub fn mdoc_zk_circuits_signature<FC>(
    fc: &FC,
) -> (
    Circuit<FC>,
    crate::core::proto::circuit::CircuitGeometry,
    crate::compile::compiler::debug::CircuitDebugSymbols,
)
where
    FC: MdocSigCompileField,
{
    crate::compile::compiler::compile(fc, |iologic| {
        let bv = crate::circuits::bitvec::BitvecLogic::new(&iologic);
        let bitvec_io = crate::circuits::bitvec::BitvecIO::new(&bv);
        let plucker =
            crate::circuits::bit_plucker::BitPlucker::<_, { K_SIG_MAC_BIT_PLUCKER }>::new(&iologic);

        let mut allocator =
            WireAllocator::new(&iologic, &bitvec_io, crate::compile::logic::K_FIRST_WIRE_POSITION);

        let curve = crate::compile::algebra::secp256r1::Secp256r1::new(fc);
        let (given, derived, pub_inputs_count, subfield_boundary_val) =
            allocate_sig(&mut allocator, &plucker, &curve);

        let mdoc_sig = MdocSignature::new(&iologic, &curve);
        let assertion = mdoc_sig.assert_signatures_and_macs(&given, &derived);
        (assertion, pub_inputs_count, subfield_boundary_val)
    })
}

pub fn generate_sig_circuit(
    p256_compile: &P256Field,
    profile: crate::mdoc::compile::LigeroProfile,
) -> Result<(Circuit<P256Field>, crate::runtime::ligero::param::LigeroConfig), String> {
    use std::fmt::Write;

    let start = std::time::Instant::now();
    let (sig_circuit_comp, stats, _symbols) = mdoc_zk_circuits_signature(p256_compile);

    let duration = start.elapsed();

    let segmented = crate::compile::compiler::segment_circuit(p256_compile, &sig_circuit_comp);
    let (num_witness, num_quadratic_constraints) =
        crate::runtime::proto::witness_and_constraint_count(&segmented);
    let p256 = crate::runtime::algebra::p256::P256Field::new();
    let p256_2 = crate::runtime::algebra::fp2::Fp2Field::new(&p256);
    let make_interpolator = crate::runtime::algebra::reed_solomon::FftInterpolatorFactory::new(
        &p256,
        &p256_2,
        p256_2.omega(),
        p256_2.omega_order(),
    );
    let best_block_enc = crate::runtime::ligero::optimize_geometry(
        num_witness,
        num_quadratic_constraints,
        profile.rateinv,
        profile.nreq,
        p256_compile.serialized_size_bytes(),
        p256_compile.serialized_size_bytes(),
        &make_interpolator,
    );
    let config = crate::runtime::ligero::param::LigeroConfig {
        rateinv: profile.rateinv,
        nreq: profile.nreq,
        block_enc: best_block_enc,
    };

    let mut hex_id = String::with_capacity(64);
    for b in sig_circuit_comp.id {
        let _ = write!(&mut hex_id, "{b:02x}");
    }

    println!("[Compiler] Signature Circuit");
    println!("  Hash (ID): 0x{hex_id}");
    println!(
        "  Geometry: nin={}, npubin={}, nout={}, W={}, T={}, L={}, assertions={}",
        stats.ninput,
        stats.npublic_input,
        stats.noutput,
        stats.nwires,
        stats.nterms,
        stats.nlayers,
        stats.nassertions
    );
    println!("  Compile time: {duration:?}");
    println!(
        "  Ligero params: rateinv={}, nreq={}, block_enc={}",
        config.rateinv, config.nreq, config.block_enc
    );

    Ok((segmented, config))
}
