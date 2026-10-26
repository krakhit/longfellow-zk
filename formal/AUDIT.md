# Formal security claims and audit

The V2 soundness chain reaches the modeled authenticated verifier with raw
proofs and a verifier-recomputed MAC key. Its checked all-budget result is

```text
Pr[both sides accept and paired extraction fails] <= (1 + N + tA) / 2^117.
```

`N` counts adversarial Fiat–Shamir queries and `tA` counts adversarial
Merkle-hash queries. The startup constant is one for every pair of query
budgets. The probability is a finite count over the shared uniform
transcript oracle and Merkle answer tape. Recommitment, arbitrary query
order, and adaptive proof selection are allowed.

## Checked endpoints

| Claim | Theorem or build target | Scope |
|---|---|---|
| V2 authenticated raw-proof extraction, all budgets | [`RawRuntimeExtraction.extraction_117`](lfzk-v2/LfzkV2/RawRuntimeExtraction.lean) | `(1+N+tA)/2^117`, under the model premises below. |
| V2 numbered leaves, `tA < 87` | `RawRuntimeExtraction.probability_numbered_merkle` | At most `(12992+tA)*(2*tA+1)/2^256`; independent of `N`. Distinct leaf inputs are an explicit premise of this stronger intermediate result. |
| V2 conservative raw-proof bound, all budgets | `RawRuntimeExtraction.extraction_114` | `(2+N+tA)/2^114`. |
| V2 annotated-proof bound | [`RuntimeExtraction`](lfzk-v2/LfzkV2/RuntimeExtraction.lean) | `(1+N+tA)/2^114` for all budgets; `(1+N+tA)/2^117` for `N ≥ 11`. The annotation is not a Rust proof field. |
| Standalone runtime Polygero hash/signature backend | [`Profile.fs_extraction_failure_127`](parameters/polygero/PolygeroRustHahn.lean) | `(N+1)/2^127`, including satisfiable transcript-dependent statements, in the ideal-binding, uniform-sampler model. Frontend, MAC, and Merkle costs are excluded here and included in the V2 composition above. |
| V1 combined extraction and false-statement soundness, all four v7 hash profiles | [`LfzkV1.FlatV7All`](lfzk-v1/LfzkV1/FlatV7All.lean) | `(1+N+tA)/2^116`, under V1's documented circuit, sampler, transcript, and MAC-key coherence premises. |
| V2 privacy components | [`PolygeroZk`](lfzk-v2/LfzkV2/PolygeroZk.lean), [`BackendEncoding`](lfzk-v2/LfzkV2/BackendEncoding.lean), [`Mac`](lfzk-v2/LfzkV2/Mac.lean) | Backend response/opening simulation and affine-tag uniformity. A complete joint frontend/backend/Merkle zero-knowledge theorem is not established. |

## V2 theorem chain

1. [`RawRuntimeExtraction.key_coherent`](lfzk-v2/LfzkV2/RawRuntimeExtraction.lean)
   derives the MAC answer from the verifier lookup. `probability` has no
   supplied-key coherence conjunct. `probability_eq_annotated` proves that
   its raw acceptance/failure event equals the annotated experiment.
2. [`TwoFieldCommitmentFS.extraction_le`](lfzk-v2/LfzkV2/TwoFieldCommitmentFS.lean)
   reduces both authenticated opening checks to one shared cut-trace
   context, adding both Merkle explanation errors. The committed oracles'
   resampling invariants are proved rather than assumed.
3. [`TwoFieldFS.extraction_le`](lfzk-v2/LfzkV2/TwoFieldFS.lean) applies the
   adaptive potential compiler to the merged MAC/hash/signature schedule.
   Each adversarial query pays the maximum local budget across roles.
4. [`TwoFieldPotential.extract_valid`](lfzk-v2/LfzkV2/TwoFieldPotential.lean)
   proves that a returned pair satisfies both circuits and agrees on its
   common message. The V2 MAC is `av*message+ap`; the two private additive
   pads may differ. A fixed pair of unequal messages collides at at most
   one multiplier. V1's shifted multiplicative tag is not used as the V2
   MAC definition.
5. [`CompiledSide`](lfzk-v2/LfzkV2/CompiledSide.lean),
   [`CompiledReplay`](lfzk-v2/LfzkV2/CompiledReplay.lean), and
   [`GradedFS`](lfzk-v2/LfzkV2/GradedFS.lean) connect decoded Polygero
   witnesses to the actual compiled frontend constraints, their product
   checks, and the trusted circuit's satisfaction predicate. False
   statements therefore cannot have a successful extracted pair.
6. [`RuntimeProfiles`](lfzk-v2/LfzkV2/RuntimeProfiles.lean),
   [`RuntimeCost`](lfzk-v2/LfzkV2/RuntimeCost.lean), and
   [`RuntimeSecurity`](lfzk-v2/LfzkV2/RuntimeSecurity.lean) discharge the
   packing, tail, and rational numerical comparisons. The annotated cost is
   `737*N/2^128 + 16383/2^128 + 18460/2^255`, before the two Merkle terms.
   Raw replay adds one verifier lookup to this count. For `tA ≥ 8`,
   `tsec_117_of_merkle_ge` absorbs that lookup and the startup cost into
   `(1+N+tA)/2^117`. For `tA < 8`,
   [`SmallMerkle`](bcs/Bcs/SmallMerkle.lean) bounds authenticated acceptance
   itself by `(2*tA^2+(12992+tA)*(2*tA+1))/2^256`, at most
   `195083/2^256`. At fixed transcript oracle, the complete prover is a
   bounded Merkle program; averaging restores arbitrary transcript
   queries without an `N` factor. One authentication path requires at
   least eight distinct queries unless a predictable child digest is hit.
   This proves the final endpoint without any additional numbering or
   leaf/node separation premise.
7. [`NumberedLeaves`](merkle/Merkle/NumberedLeaves.lean) also proves the
   stronger opening-count argument: 87 distinct leaf inputs require 87
   distinct queries unless a verifier query hits a predictable digest.
   The counted event includes the leaf-input distinctness and opening
   count. `probability_numbered_merkle` derives the count of 87 from
   compiled acceptance and the runtime hash geometry.

The extractor is a mathematical search in the two lists associated with
the committed oracles. The theorem bounds acceptance without a matching
satisfying pair; it does not claim that decoding the Rust proof bytes alone
efficiently recovers a witness.

## Premises and implementation boundary

The numerical endpoints retain the following explicit premises:

- Hash geometry `(n,k,s,t) = (3584,512,18,87)` and signature geometry
  `(2912,416,15,86)`, with the instance's distinct evaluation points and
  decoder/column encodings.
- Hash and MAC fields of size at least `2^128`, signature field size at
  least `2^255`, and Merkle digest alphabet of size exactly `2^256`.
- Balanced finite samplers for every frontend block, backend coin,
  opening-query role, and the MAC multiplier, on one common transcript
  answer alphabet. These are ideal sampler assumptions, not a claim that
  every challenge tuple is one 256-bit digest.
- Trusted circuit layouts and public/private input embeddings. Output
  dimensions are at most 5 and 3; sharp frontend budgets are at most 655
  and 552. For every satisfying committed candidate, the two circuit MAC
  rows agree with the shared public tag. These correspondence premises
  are not consequences of a backend numerical certificate.
- The declared Merkle codec and role decoders, and enough finite answer
  tape for the bounded execution: `TM ≥ tA + 12992`.

The runtime's [`polygero/src/hash.rs`](../rust/runtime/polygero/src/hash.rs)
prefixes leaves with `polygero/root/original-leaf/v1` and internal nodes
with `polygero/root/node/v1`. Each leaf includes the context, its column
index as a little-endian `u64`, the salt, and canonical column bytes.
[`verifier.rs`](../rust/runtime/polygero/src/verifier.rs) hashes each opened
column with its sampled index before verifying the Merkle paths;
[`transcript.rs`](../rust/runtime/polygero/src/transcript.rs) samples
distinct indices. Thus repeated column values do not identify leaf
preimages at different positions. `OpeningClaim.DistinctLeafInputs` is the
explicit codec correspondence premise for the stronger 87-query lemma;
`distinctLeafInputs_of_index` derives it from an index decoder. The final
all-budget theorem uses the weaker path-depth argument and does not need
this extra correspondence premise. Neither argument assumes 87 independent
digest guesses: the bound retains the predictable-target counting factor.

This is end-to-end soundness for the stated mathematical verifier model.
It is not source-level verification of Rust or C++. Limb arithmetic,
overflow, allocation bounds, parser validation, serialization, domain/hash
encodings, and the concrete SHA/AES expansion and rejection samplers remain
implementation correspondence obligations. The replay model preserves the
protocol's challenge order and prefixes; byte-level transcript equivalence
is outside the theorem. The individual registered application's circuit
semantics must also be related to the modeled trusted circuit.

V2 joint-view zero knowledge still needs the frontend's causal transmission
and commitment-dependent pads combined with the backend simulator and
Merkle-hiding/oracle-programming hybrids. The documentation makes no full
V2 privacy claim.

## Reproduce the audit

From `formal/`, after installing the pinned Lean toolchain and Mathlib:

```sh
lake build
rustc --edition 2024 scripts/audit.rs -o /tmp/longfellow-source-audit
/tmp/longfellow-source-audit
lake env lean scripts/Audit.lean
cargo run --release --manifest-path lfzk-v1/scripts/Cargo.toml --bin inspect-v7-profile
cargo run --release --manifest-path lfzk-v1/scripts/Cargo.toml --bin inspect-v7-assertions
```

The default build includes all retained Hahn certificate families, both
sumcheck libraries, the four V1 116-bit endpoints, the V2 endpoint audit,
and the Polygero API/dependency checks. `scripts/build.sh` uses Lake's default
concurrency. There is no separate certificate build requirement.

The Rust source scanner strips nested Lean comments and strings before
rejecting unchecked proof constructs. It also validates local Markdown
links in the formal and Rust documentation. The Lean audit inspects every
imported declaration owned by the V1/V2, sumcheck, BCS, Merkle, Polygero,
runtime-Hahn, and runtime-profile modules, including private helpers.
V2 and the other audited non-V1 modules permit only `propext`,
`Classical.choice`, and `Quot.sound`. V1 numerical rows retain the documented
native-evaluation allowance, including their imported legacy numerical
certificates. V2 and the retained Hahn identities do not depend on that
allowance.

The broad audit is separate from the default build so repeated incremental
builds keep their short API and certificate checks. These checks establish
the stated proof dependencies and exact numerical facts; they do not
discharge the implementation correspondence premises above.

The V1 Rust inspectors load the frozen archives through the current
single-crate runtime, recompute archive and circuit IDs, compare the five
recorded circuit/geometry profiles, and reject violations of the structural
assertion premises. The older Python launchers targeting the former crate
layout have been removed. The remaining legacy numerical reporting scripts
do not participate in the trusted Lean proof chain.
