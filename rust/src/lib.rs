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

/// Conditionally includes items when `feature = "compiler"` (or `test`) is active.
macro_rules! cfg_compiler {
    ($($item:item)*) => {
        $(
            #[cfg(any(test, feature = "compiler"))]
            $item
        )*
    };
}

/// Conditionally includes items when `feature = "prover"` (or `test`) is active.
macro_rules! cfg_prover {
    ($($item:item)*) => {
        $(
            #[cfg(any(test, feature = "prover"))]
            $item
        )*
    };
}

/// Conditionally includes items when `feature = "verifier"` (or `test`) is active.
macro_rules! cfg_verifier {
    ($($item:item)*) => {
        $(
            #[cfg(any(test, feature = "verifier"))]
            $item
        )*
    };
}

/// Conditionally includes items when `feature = "prover"` or `feature = "compiler"` (or `test`) is
/// active.
macro_rules! cfg_prover_or_compiler {
    ($($item:item)*) => {
        $(
            #[cfg(any(test, feature = "prover", feature = "compiler"))]
            $item
        )*
    };
}

/// Conditionally includes items when `feature = "testonly"` (or `test`) is active.
macro_rules! cfg_testonly {
    ($($item:item)*) => {
        $(
            #[cfg(any(test, feature = "testonly"))]
            $item
        )*
    };
}

#[path = "../util/src/lib.rs"]
pub(crate) mod util;

#[path = "../core"]
pub mod core {
    #[path = "algebra/src/lib.rs"]
    pub mod algebra;
    #[path = "proto/src/lib.rs"]
    pub mod proto;
}

#[path = "../runtime"]
pub mod runtime {
    #[path = "algebra/src/lib.rs"]
    pub mod algebra;
    #[path = "ligero/src/lib.rs"]
    pub mod ligero;
    #[path = "merkle/src/lib.rs"]
    pub mod merkle;
    #[path = "proto/src/lib.rs"]
    pub mod proto;
    #[path = "random/src/lib.rs"]
    pub mod random;
    #[path = "sumcheck/src/lib.rs"]
    pub mod sumcheck;
    #[path = "zk/src/lib.rs"]
    pub mod zk;
}

cfg_compiler! {
    #[path = "../compile"]
    pub mod compile {
        #[path = "algebra/src/lib.rs"]
        pub mod algebra;
        #[path = "compiler/src/lib.rs"]
        pub mod compiler;
        #[path = "logic/src/lib.rs"]
        pub mod logic;
        #[path = "proto/src/lib.rs"]
        pub mod proto;

        cfg_testonly! {
            #[path = "eval/src/lib.rs"]
            pub mod eval;
        }
    }
}

#[path = "../circuits"]
pub mod circuits {
    #[path = "analog_decoder/src/lib.rs"]
    pub mod analog_decoder;
    #[path = "bit_plucker/src/lib.rs"]
    pub mod bit_plucker;

    cfg_prover_or_compiler! {
        #[path = "ec/src/lib.rs"]
        pub mod ec;
        #[path = "ecdsa2/src/lib.rs"]
        pub mod ecdsa2;
        #[path = "mac/src/lib.rs"]
        pub mod mac;
        #[path = "sha256/src/lib.rs"]
        pub mod sha256;
        #[path = "sha256msg/src/lib.rs"]
        pub mod sha256msg;
    }

    cfg_compiler! {
        #[path = "analog_adder/src/lib.rs"]
        pub mod analog_adder;
        #[path = "arithmetic/src/lib.rs"]
        pub mod arithmetic;
        #[path = "big_bitvec/src/lib.rs"]
        pub mod big_bitvec;
        #[path = "bignum/src/lib.rs"]
        pub mod bignum;
        #[path = "bitvec/src/lib.rs"]
        pub mod bitvec;
        #[path = "boolean/src/lib.rs"]
        pub mod boolean;
        #[path = "gf2_128/src/lib.rs"]
        pub mod gf2_128;
        #[path = "lookup/src/lib.rs"]
        pub mod lookup;
        #[path = "mac_gf128/src/lib.rs"]
        pub mod mac_gf128;
        #[path = "memcmp/src/lib.rs"]
        pub mod memcmp;
        #[path = "polynomial/src/lib.rs"]
        pub mod polynomial;
        #[path = "routing/src/lib.rs"]
        pub mod routing;
    }

    cfg_testonly! {
        #[path = "experimental/src/lib.rs"]
        pub mod experimental;
    }
}

#[cfg(feature = "mdoc")]
#[path = "../applications/mdoc_zk"]
pub mod mdoc {
    #[path = "circuits/src/lib.rs"]
    pub mod circuits;
    #[path = "proto/src/lib.rs"]
    pub mod proto;
    #[path = "runtime/src/lib.rs"]
    pub mod runtime;

    /// Curated top-level mdoc API. Everything else stays reachable through the sub-modules
    /// (`mdoc::runtime`, `mdoc::circuits`, `mdoc::proto`, ...).
    pub use runtime::{
        circuit_supports, decompress_circuits, find_zk_spec, find_zk_spec_by_hex,
        is_supported_version, ligero_configs, req_attr, same_namespace, MdocProof,
        MdocProofGeometry, MdocProverErrorCode, MdocVerifierErrorCode, RequestedAttribute,
        ZkSpecStruct, CURRENT_VERSION, CURRENT_ZK_SPECS, NUM_CURRENT_ZK_SPECS, NUM_ZK_SPECS,
        ZK_SPECS,
    };

    cfg_prover! {
        pub use runtime::{run_mdoc_prover, run_mdoc_prover_inner};
    }

    cfg_verifier! {
        pub use runtime::{run_mdoc_verifier, run_mdoc_verifier_inner};
    }

    cfg_compiler! {
        #[path = "artifacts/src/lib.rs"]
        pub mod artifacts;
        #[path = "compile/src/lib.rs"]
        pub mod compile;
    }

    cfg_testonly! {
        #[path = "testcases/src/lib.rs"]
        pub mod testcases;
    }
}

/// Enforces the internal module dependency DAG and architectural layer boundaries across the
/// single `longfellow-zk` crate.
///
/// Because Rust allows modules within the same crate to mutually reference each other (`crate::*`),
/// consolidating multiple workspace sub-crates into a single crate removes Cargo's automatic
/// crate-level cycle and layer enforcement. This test module restores that guarantee at `cargo
/// test` time by statically scanning every library source file (`src/**/*.rs`, excluding
/// `#[cfg(test)]` tails and standalone `bin/` targets) and verifying two invariants:
///
/// 1. **Strict Architectural Layering**: Every sub-module belongs to one of six ordered
///    architectural layers:
///    - Layer 0 (`util`): Low-level bit/array/Morton helpers with zero internal dependencies.
///    - Layer 1 (`core::*`): Core algebraic traits, field/curve definitions, and circuit/archive
///      formats.
///    - Layer 2 (`runtime::*`): Prover and verifier runtime protocols (algebra, transcript, Merkle,
///      Sumcheck, Ligero, ZK).
///    - Layer 3 (`compile::*`): Circuit synthesis backend, wire allocation, and compile-time logic.
///    - Layer 4 (`circuits::*`): Reusable cryptographic sub-circuits (SHA-256, ECDSA, MAC,
///      BitPlucker, etc.).
///    - Layer 5 (`mdoc::*`): ISO 18013-5 mDoc application circuits, runtime, and artifacts.
///
///    A module in layer $L$ may only import modules in layer $L' \le L$. Any upward import
///    (for example, `core::proto` importing `compile::algebra`, or `runtime::zk` importing
///    `circuits::*`) causes an immediate test failure identifying the offending file and import.
///
/// 2. **Acyclic Module Dependency Graph (DAG)**: Even within the same layer (e.g., among
///    `circuits::*` or `runtime::*` sub-modules), the directed graph of
///    `crate::<layer>::<submodule>` references must be a strict DAG with no cycles. Depth-first
///    cycle detection (`has_cycle`) reports the exact cycle path if one is introduced.
#[cfg(test)]
mod module_dag_tests {
    use std::{
        collections::{BTreeMap, BTreeSet},
        fs,
        path::{Path, PathBuf},
    };

    /// Recursively collects all `.rs` source files under `dir`, skipping standalone binary targets
    /// (`bin/`).
    fn collect_rs_files(dir: &Path, out: &mut Vec<PathBuf>) {
        let Ok(entries) = fs::read_dir(dir) else {
            return;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                if path.file_name().and_then(|n| n.to_str()) == Some("bin") {
                    continue;
                }
                collect_rs_files(&path, out);
            } else if path.extension().and_then(|e| e.to_str()) == Some("rs") {
                out.push(path);
            }
        }
    }

    /// Recursively parses a path or braced `use` tree following `crate::` (e.g.,
    /// `crate::runtime::proto`, `crate::runtime::{merkle::..., proto::...}`, or
    /// `crate::{circuits::ec::..., compile::{algebra::..., logic::...}}`) and records every
    /// referenced `<layer>::<submodule>` (or `util`) into `deps`.
    fn parse_crate_tree(raw: &str, layer_prefix: Option<&str>, deps: &mut BTreeSet<String>) {
        let s = raw.trim_start();
        if let Some(inner) = s.strip_prefix('{') {
            let mut depth = 1usize;
            let mut item_start = 0;
            for (idx, ch) in inner.char_indices() {
                match ch {
                    '{' => depth += 1,
                    '}' => {
                        depth -= 1;
                        if depth == 0 {
                            parse_crate_tree(&inner[item_start..idx], layer_prefix, deps);
                            break;
                        }
                    }
                    ',' if depth == 1 => {
                        parse_crate_tree(&inner[item_start..idx], layer_prefix, deps);
                        item_start = idx + 1;
                    }
                    _ => {}
                }
            }
            return;
        }

        let ident: String = s
            .chars()
            .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
            .collect();
        if ident.is_empty() {
            return;
        }
        let rest = &s[ident.len()..];
        match layer_prefix {
            None => {
                if ident == "util" {
                    deps.insert("util".to_string());
                } else if matches!(
                    ident.as_str(),
                    "core" | "runtime" | "compile" | "circuits" | "mdoc"
                ) {
                    if let Some(after_colons) = rest.strip_prefix("::") {
                        parse_crate_tree(after_colons, Some(&ident), deps);
                    }
                }
            }
            Some(layer) => {
                if ident != "self" {
                    deps.insert(format!("{layer}::{ident}"));
                }
            }
        }
    }

    /// Scans Rust source text for `crate::<layer>::<submodule>` paths (including braced
    /// `use crate::{...}` trees) and returns the set of top-level sub-modules referenced by `src`.
    fn extract_crate_deps(src: &str) -> BTreeSet<String> {
        let mut deps = BTreeSet::new();
        let bytes = src.as_bytes();
        let needle = b"crate::";
        let mut i = 0;
        while i + needle.len() <= bytes.len() {
            if &bytes[i..i + needle.len()] == needle
                && (i == 0 || !(bytes[i - 1].is_ascii_alphanumeric() || bytes[i - 1] == b'_'))
            {
                let rest = &src[i + needle.len()..];
                parse_crate_tree(rest, None, &mut deps);
                i += needle.len();
            } else {
                i += 1;
            }
        }
        deps
    }

    /// Performs depth-first cycle detection starting from `node` in `graph`.
    /// Returns `Some(cycle_path)` if a directed cycle is found, or `None` if the subgraph is
    /// acyclic.
    fn has_cycle(
        node: &str,
        graph: &BTreeMap<String, BTreeSet<String>>,
        visiting: &mut BTreeSet<String>,
        visited: &mut BTreeSet<String>,
        path: &mut Vec<String>,
    ) -> Option<Vec<String>> {
        if visiting.contains(node) {
            path.push(node.to_string());
            return Some(path.clone());
        }
        if visited.contains(node) {
            return None;
        }
        visiting.insert(node.to_string());
        path.push(node.to_string());
        if let Some(neighbors) = graph.get(node) {
            for next in neighbors {
                if let Some(cycle) = has_cycle(next, graph, visiting, visited, path) {
                    return Some(cycle);
                }
            }
        }
        path.pop();
        visiting.remove(node);
        visited.insert(node.to_string());
        None
    }

    /// Verifies that:
    /// 1. No production source file in any module imports a module from a higher architectural
    ///    layer (`util` < `core` < `runtime` < `compile` < `circuits` < `mdoc`).
    /// 2. The full directed dependency graph across all 41 sub-modules contains no cycles.
    #[test]
    fn test_module_dependency_dag_and_layer_boundaries() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"));
        let modules = [
            ("util", "util/src"),
            ("core::algebra", "core/algebra/src"),
            ("core::proto", "core/proto/src"),
            ("runtime::algebra", "runtime/algebra/src"),
            ("runtime::proto", "runtime/proto/src"),
            ("runtime::random", "runtime/random/src"),
            ("runtime::merkle", "runtime/merkle/src"),
            ("runtime::sumcheck", "runtime/sumcheck/src"),
            ("runtime::ligero", "runtime/ligero/src"),
            ("runtime::zk", "runtime/zk/src"),
            ("compile::algebra", "compile/algebra/src"),
            ("compile::proto", "compile/proto/src"),
            ("compile::logic", "compile/logic/src"),
            ("compile::compiler", "compile/compiler/src"),
            ("compile::eval", "compile/eval/src"),
            ("circuits::analog_adder", "circuits/analog_adder/src"),
            ("circuits::analog_decoder", "circuits/analog_decoder/src"),
            ("circuits::arithmetic", "circuits/arithmetic/src"),
            ("circuits::bitvec", "circuits/bitvec/src"),
            ("circuits::bit_plucker", "circuits/bit_plucker/src"),
            ("circuits::bignum", "circuits/bignum/src"),
            ("circuits::big_bitvec", "circuits/big_bitvec/src"),
            ("circuits::boolean", "circuits/boolean/src"),
            ("circuits::ec", "circuits/ec/src"),
            ("circuits::ecdsa2", "circuits/ecdsa2/src"),
            ("circuits::gf2_128", "circuits/gf2_128/src"),
            ("circuits::lookup", "circuits/lookup/src"),
            ("circuits::mac", "circuits/mac/src"),
            ("circuits::mac_gf128", "circuits/mac_gf128/src"),
            ("circuits::memcmp", "circuits/memcmp/src"),
            ("circuits::polynomial", "circuits/polynomial/src"),
            ("circuits::routing", "circuits/routing/src"),
            ("circuits::sha256", "circuits/sha256/src"),
            ("circuits::sha256msg", "circuits/sha256msg/src"),
            ("circuits::experimental", "circuits/experimental/src"),
            ("mdoc::proto", "applications/mdoc_zk/proto/src"),
            ("mdoc::circuits", "applications/mdoc_zk/circuits/src"),
            ("mdoc::compile", "applications/mdoc_zk/compile/src"),
            ("mdoc::runtime", "applications/mdoc_zk/runtime/src"),
            ("mdoc::testcases", "applications/mdoc_zk/testcases/src"),
            ("mdoc::artifacts", "applications/mdoc_zk/artifacts/src"),
        ];

        let layer_rank = |mod_name: &str| -> u8 {
            if mod_name == "util" {
                0
            } else if mod_name.starts_with("core::") {
                1
            } else if mod_name.starts_with("runtime::") {
                2
            } else if mod_name.starts_with("compile::") {
                3
            } else if mod_name.starts_with("circuits::") {
                4
            } else if mod_name.starts_with("mdoc::") {
                5
            } else {
                panic!("Unknown module {mod_name}")
            }
        };

        let mut graph: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        for (mod_name, rel_dir) in modules {
            let mut files = Vec::new();
            collect_rs_files(&root.join(rel_dir), &mut files);
            let mut deps = BTreeSet::new();
            for f in files {
                let content = fs::read_to_string(&f).expect("read rs file");
                // Strip inline #[cfg(test)] tail before checking library module DAG
                let prod_content = content.split("#[cfg(test)]").next().unwrap_or(&content);
                for dep in extract_crate_deps(prod_content) {
                    if dep != mod_name {
                        assert!(
                            layer_rank(&dep) <= layer_rank(mod_name),
                            "Layer violation: {mod_name} ({}) imports higher-layer module {dep}",
                            f.display()
                        );
                        deps.insert(dep);
                    }
                }
            }
            graph.insert(mod_name.to_string(), deps);
        }

        let mut visiting = BTreeSet::new();
        let mut visited = BTreeSet::new();
        let mut path = Vec::new();
        for node in graph.keys() {
            if let Some(cycle) = has_cycle(node, &graph, &mut visiting, &mut visited, &mut path) {
                panic!("Module dependency cycle detected: {}", cycle.join(" -> "));
            }
        }
    }
}
