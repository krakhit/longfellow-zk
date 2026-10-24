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

//! Shared layout of the selected SHAKE256 witnesses.

pub(crate) const SHAKE256_RATE: usize = 136;
pub(crate) const KECCAK_ROUNDS: usize = 24;
// State snapshots after the first round, then after each group of four rounds.
pub(crate) const STATE_ROUNDS: [usize; 7] = [0, 3, 7, 11, 15, 19, 23];
