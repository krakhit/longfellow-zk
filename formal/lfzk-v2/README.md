# Longfellow V2: extraction and soundness

This library models the trusted-circuit path in `rust/runtime/sumcheck-v2`
and `rust/runtime/zk-v2`. It composes the projective sumcheck frontend,
nonrecursive Polygero, two authenticated side proofs, and V2's affine MAC
on one adaptive Fiat–Shamir transcript.

## Strongest checked results

| Result | Bound and scope | Endpoint |
|---|---|---|
| Authenticated two-field extraction, all query budgets | **117-bit security:** `Pr[accept ∧ paired extraction fails] ≤ (1+N+tA)/2^117`. Raw proofs use the verifier-recomputed MAC key. | [`RawRuntimeExtraction.extraction_117`](LfzkV2/RawRuntimeExtraction.lean) |
| Numbered leaves, `tA < 87` | At most `(12992+tA)*(2*tA+1)/2^256`, independent of `N`, assuming distinct leaf inputs. | `RawRuntimeExtraction.probability_numbered_merkle` |
| Standalone runtime Polygero hash/signature backend | `(N+1)/2^127` in the ideal-binding, uniform-sampler FS model, including transcript-dependent satisfiable statements. | [`Profile.fs_extraction_failure_127`](../parameters/polygero/PolygeroRustHahn.lean), `Profile.fs_soundness_127` |
| Backend privacy components | One tape bijection preserves both complete response polynomials and all opened core/mask columns; exact joint distributions support statements and coins chosen from the opened view. | [`PolygeroZk.sameDistribution_adaptive`](LfzkV2/PolygeroZk.lean), [`BackendEncoding.compatible_compiled`](LfzkV2/BackendEncoding.lean) |

`N` counts adversarial transcript queries and `tA` counts adversarial
Merkle-hash queries. Both bounds allow arbitrary query order, recommitment,
grinding, and adaptive proof selection. The full composition includes the
frontend, MAC, and both Merkle explanation errors. The standalone backend
bound covers only that component.

The all-budget numerator has startup constant one. The proof charges the
verifier's key lookup as one extra query. Eight Merkle queries cover that
lookup and the composition's startup cost; fewer queries require a digest
guess to explain even one authentication path. This final result does not
require a numbered-leaf assumption. Numbered leaves, as in the runtime,
strengthen the digest-guessing threshold to 87 queries. The complete V2
joint-view zero-knowledge theorem remains open.

## End-to-end theorem chain

1. [`RawRuntimeExtraction.key_coherent`](LfzkV2/RawRuntimeExtraction.lean)
   derives the key answer from verifier replay.
   `probability_eq_annotated` proves equality between the raw acceptance
   and extraction-failure event and the annotated experiment. The final
   raw event has no supplied-key coherence premise.
2. [`TwoFieldCommitmentFS.extraction_le`](LfzkV2/TwoFieldCommitmentFS.lean)
   reduces both authenticated opening checks to the same cut-trace
   context, adding both Merkle explanation errors. Context resampling
   invariance follows from the common execution.
3. [`TwoFieldFS.extraction_le`](LfzkV2/TwoFieldFS.lean) applies the
   rational potential compiler to the merged MAC/hash/signature schedule.
   Every adversarial query pays the maximum local cost across roles.
   [`GradedBudgets`](LfzkV2/GradedBudgets.lean) and
   [`GradedCost`](LfzkV2/GradedCost.lean) prove the slot sums and their
   normalization by the full answer alphabet.
4. [`TwoFieldPotential.extract_valid`](LfzkV2/TwoFieldPotential.lean)
   proves that a returned pair satisfies both actual circuit predicates
   and agrees on the common message. The two private MAC pads may differ.
5. [`CompiledSide`](LfzkV2/CompiledSide.lean),
   [`CompiledReplay`](LfzkV2/CompiledReplay.lean), and
   [`GradedFS`](LfzkV2/GradedFS.lean) connect accepted Polygero openings and
   decoded witnesses to the compiled frontend constraints, pad-product
   checks, and trusted-circuit satisfaction.
6. [`RuntimeProfiles`](LfzkV2/RuntimeProfiles.lean),
   [`RuntimeCost`](LfzkV2/RuntimeCost.lean), and
   [`RuntimeSecurity`](LfzkV2/RuntimeSecurity.lean) supply the exact
   packing, tail, and rational comparisons used by the final endpoint.

The extractor searches finite lists associated with the committed
oracles. Every successful pair satisfies both circuits with equal common
values, so a false statement cannot have a successful extracted pair.
Efficient witness recovery from Rust proof bytes alone is outside the
theorem.

## Frontend and compiler correctness

The algebraic model follows the V2 projective convention:
`C = c0+c2` and `z²*C+(1-z²)*c0+z*c1`. It is valid in characteristic two
and does not require a third interpolation node.

| Result | Checked interface |
|---|---|
| Exact constraint construction, malformed-length rejection, and public/private input reconstruction | [`buildConstraints_correct`](LfzkV2/Constraints.lean), [`compiled_iff_clear`](LfzkV2/Compiler.lean), [`compiled_circuit_reduction`](LfzkV2/Inputs.lean) |
| Complete trusted circuit and honest prover, including zero outputs and intermediate assertion failures | [`CircuitLayer.effective_truth`](LfzkV2/Circuit.lean), [`Circuit.soundness_reduction`](LfzkV2/Program.lean), [`Circuit.prove_complete`](LfzkV2/Prover.lean) |
| Concrete prefix replay and whole-block adaptive challenge accounting | [`Schedule`](LfzkV2/Schedule.lean), [`HashReplay`](LfzkV2/HashReplay.lean), [`FrontendFS`](LfzkV2/FrontendFS.lean) |
| Polygero statement and product-copy compatibility derived from the actual compiler | [`Backend.decoded_compiled`](LfzkV2/Backend.lean), [`BackendEncoding.compatible_compiled`](LfzkV2/BackendEncoding.lean) |

Each output/assertion/combine test has at most one bad field value and
each sumcheck round at most two. Only the last nonzero assertion residual
is selected. The sharp frontend budget is
`logv + sum_layers(min(1, assertions) + 2*logw + 1)`.

The pad-product layout is fixed by the trusted circuit, independently
of proof messages. Product consistency is indispensable: the API checks
include a witness whose affine equations pass while its product checks
and clear verifier reject.

## Runtime parameters and numerical accounting

| Side | `n` | `k` | `s` | Openings | Committed-list bound |
|---|---:|---:|---:|---:|---:|
| Hash | 3584 | 512 | 18 | 87 | 22 |
| Signature | 2912 | 416 | 15 | 86 | 33 |

With the field, sampler, and circuit-budget premises below, the exact
normalized field/MAC cost for the annotated experiment is at most

```text
737*N/2^128 + 16383/2^128 + 18460/2^255.
```

Raw verifier replay adds one lookup to that accounting. The two Merkle
explanation errors are included by the numerical extraction endpoint.
The small-budget proof fixes the transcript oracle, bounds the resulting
Merkle program, then averages over transcript oracles. Its bound therefore
has no transcript-query factor, even with arbitrary query interleaving.
All retained Hahn and runtime backend certificates build by default.

V2 defines `tag = av*message+ap` directly. For fixed unequal messages and
separate fixed additive pads, the two tags agree at at most one multiplier.
Translating a fresh pad gives exact tag uniformity. These facts are proved
in [`Mac`](LfzkV2/Mac.lean).

## Assumptions and deployment boundary

The numerical theorem retains explicit premises for:

- The runtime geometries above, distinct evaluation points, and the
  Polygero decoder/column encodings.
- Hash and MAC field sizes at least `2^128`, signature field size at
  least `2^255`, and Merkle digest alphabet of size exactly `2^256`.
- Balanced samplers for the actual frontend challenge blocks, backend
  coins and fixed-size query sets, and the MAC key, on one common ideal
  transcript alphabet.
- Trusted circuit and pad layouts, public/private input embeddings,
  output dimensions at most 5 and 3, and sharp frontend budgets at most
  655 and 552. Every satisfying committed candidate must enforce its
  circuit's MAC equation and the shared public tag.
- The Merkle codecs and role decoders, with enough answer tape:
  `TM ≥ tA+12992`.

The proof is end to end for this mathematical verifier model. Identifying
Rust circuit data, byte-level transcript encodings, parser behavior,
field arithmetic, allocation bounds, and SHA/AES expansion/rejection
sampling with that model remains an implementation correspondence task.
The [formal audit](../AUDIT.md) records this boundary and the shared
verification commands.

## Privacy status

The joint Polygero simulator preserves both full responses and all opened
columns, including adaptive statements read from those openings.
Compiler compatibility follows from the actual V2 rows and product-slot
encoding. The affine MAC has exact tag-uniformity theorems.

Complete joint-view zero knowledge still requires the frontend's causal
transmission and commitment-dependent pads to be combined with that
backend simulator and the Merkle-hiding/oracle-programming hybrids.
No full V2 privacy theorem is claimed.

## Reproduce the checks

From `formal/`:

```sh
lake build
lake build LfzkV2.APITest
rustc --edition 2024 scripts/audit.rs -o /tmp/longfellow-source-audit
/tmp/longfellow-source-audit
lake env lean scripts/Audit.lean
```

The V2 endpoint audit and retained certificates are in the default
build. V2 proofs permit only Lean's standard `propext`, `Classical.choice`,
and `Quot.sound` axioms. The API checks cover scalar and empty proofs,
mismatched round counts, assertion failures with zero outputs, committed
slot offsets, and the product-consistency boundary.
