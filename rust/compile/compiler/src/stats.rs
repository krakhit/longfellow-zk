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

//! Version-neutral reporting of circuit geometry; no compilation policy.

use crate::{
    compile::algebra::field::CompileField,
    core::proto::circuit::{Circuit, CircuitGeometry},
};

pub fn dump_stats<F: CompileField + crate::core::algebra::SerializableField>(
    name: &str,
    _circuit: &Circuit<F>,
    info: &CircuitGeometry,
) {
    println!(
        "{}: nin:{} pubin:{} nout:{} w:{} w+in:{} t:{} l:{} assertions:{}",
        name,
        info.ninput,
        info.npublic_input,
        info.noutput,
        info.nwires,
        info.ninput + info.nwires,
        info.nterms,
        info.nlayers,
        info.nassertions,
    );
}
