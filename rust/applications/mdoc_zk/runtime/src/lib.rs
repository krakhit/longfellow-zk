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

pub mod attribute;
pub(in crate::mdoc::runtime) mod concrete;
pub mod error;
pub mod proto;
pub(in crate::mdoc::runtime) mod utils;
pub mod zk_spec;

pub use attribute::RequestedAttribute;
pub use concrete::{push_input_hash, push_input_sig};
pub use error::{MdocProverErrorCode, MdocVerifierErrorCode};
pub use proto::*;
pub use utils::{circuit_supports, parse_hex_nat, parse_pk_coordinate, req_attr, same_namespace};
pub use zk_spec::*;

pub use crate::mdoc::{
    circuits,
    proto::{config, *},
};

cfg_compiler! {
    pub mod provider;

    pub use {
        self::provider::*,
        crate::mdoc::{compile as generate, compile::*},
    };
}

cfg_prover! {
    pub(in crate::mdoc::runtime) mod mac;
    pub mod prover;

    pub use self::{
        concrete::{push_witness_hash, push_witness_sig},
        mac::{generate_mac_ap, push_macs},
        prover::*,
    };
}

cfg_verifier! {
    pub mod verifier;

    pub use verifier::*;
}

#[cfg(test)]
#[path = "../tests/all/mod.rs"]
mod tests_all;
