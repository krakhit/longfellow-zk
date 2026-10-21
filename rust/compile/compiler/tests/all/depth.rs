// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::compile::algebra::p256::P256Field;
use crate::compile::eval::eval_circuit_fc;
use crate::compile::logic::{Logic, LogicIO};
use crate::core::algebra::AlgebraicField;
use crate::core::proto::FieldID;
use crate::runtime::algebra::p256::P256Field as RuntimeP256Field;

#[test]
fn test_direct_input_assertion_has_one_layer() {
    let f = P256Field::new();
    let (circuit, geometry, symbols) = crate::compile::compiler::compile(&f, |logic| {
        let x = logic.input(1);
        let assertion = logic.assert0("input", &x);
        (assertion, 1, 0)
    });
    assert_eq!(geometry.nlayers, 1);

    let runtime_f = RuntimeP256Field::new();
    eval_circuit_fc(
        &f,
        &runtime_f,
        &circuit,
        &symbols,
        &[runtime_f.one(), runtime_f.zero()],
        FieldID::P256,
    )
    .unwrap()
    .assert_all_passed();

    let failed = eval_circuit_fc(
        &f,
        &runtime_f,
        &circuit,
        &symbols,
        &[runtime_f.one(), runtime_f.one()],
        FieldID::P256,
    )
    .unwrap();
    assert!(failed.is_err());
}
