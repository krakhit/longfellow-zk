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

//! Heap measurements for the MLDSA benchmark.
#[path = "../../../../benches/support/memory.rs"]
mod tracking;
use tracking::{get_current_allocated, get_peak_allocated, reset_peak};

pub(super) struct Measurement {
    baseline: usize,
}

pub(super) struct HeapPeak {
    pub(super) baseline: usize,
    pub(super) high: usize,
}

impl Measurement {
    pub(super) fn start() -> Self {
        let baseline = get_current_allocated();
        reset_peak();
        Self { baseline }
    }

    pub(super) fn finish(self) -> HeapPeak {
        HeapPeak {
            baseline: self.baseline,
            high: get_peak_allocated(),
        }
    }
}

impl HeapPeak {
    pub(super) fn additional(&self) -> usize {
        self.high.saturating_sub(self.baseline)
    }
}
