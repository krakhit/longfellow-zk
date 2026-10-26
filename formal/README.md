# Formal verification

**The modeled v7 Longfellow verifier using Ligero V1 has 116-bit T-security.** For the
signature and SHA circuits with one through four attributes on one
Fiat–Shamir transcript, the certified soundness error is at most
`(1 + tA + N) / 2^116`, where `tA` and `N` are the Merkle- and
transcript-oracle query budgets. The extraction theorems and their
false-statement soundness corollaries are checked by
[`LfzkV1.FlatV7All`](lfzk-v1/LfzkV1/FlatV7All.lean) in the default build.
Their premises and deployment boundary are stated in the
[Longfellow README](lfzk-v1/README.md).

The 116-bit proof uses flat extraction for zero transcript queries and a
graded extraction bound for positive query counts.

Version 7 uses Ligero V1; version 8 uses Polygero. The
[Ligero README](ligero/README.md) documents the component analysis.

The default `lake build` includes all 16 retained Hahn/Delsarte certificate
families: five runtime Polygero profiles, six v7 Ligero mask certificates, and
five Polygero benchmark certificates. It also checks their numerical endpoints
and an [axiom audit](parameters/hahn/RuntimeHahn/APITest.lean). The Hahn identities
use exact integer checks and a proved polynomial interpolation theorem; no
native-evaluation axiom is needed for the certificates.

Run `lake build` or `scripts/build.sh` from this directory to build the default
targets with Lean and Lake's default concurrency. The script also accepts individual Lake targets.

The Ligero development proves:

- Reed–Solomon code distance, affine triple-counting and selected-MCA bounds,
  and JB agreement with checked η³ threshold parameters.
- Delsarte's LP bound using Hahn kernels for uniform intersection families,
  with Johnson as the degree-one case. It certifies the V1 unchecked-mask list
  below the Johnson threshold.
- Response-assisted scalar IOP extraction for Ligero V1, together
  with response-uniform envelopes and false-statement soundness.
- Merkle prefix binding and typed Fiat–Shamir query bookkeeping.
- Exact IOP certificates for v7 signature and hash geometries, and local
  challenge/query count certificates for the hash
  geometries and V1 signatures.

See the [Ligero README](ligero/README.md) for component theorem names and
certificates. This package also contains the EC/ECDSA circuit development and
two sumcheck libraries:

- [Sumcheck V1](sumcheck-v1/SumcheckV1/README.md), imported as `SumcheckV1`,
  contains the legacy round, chain, and challenge-tape proofs used by `LfzkV1`.
- [Sumcheck V2](sumcheck-v2/README.md), imported as `SumcheckV2`, proves the
  projective round update, honest table folding, single-hand layer reduction,
  masked constraint equations, and challenge-tape bounds. These are component
  theorems; the `LfzkV1` security certificates above still use V1.

[Longfellow V2](lfzk-v2/README.md), imported as `LfzkV2`, connects the V2
builder, compiler, trusted circuit evaluation, assertions, and honest prover.
It connects the Polygero decoder to the compiled constraints and proves a
candidate-family composition on one adaptive Fiat–Shamir oracle. The
ideal-binding backend extraction term is proved for transcript-dependent
statements, and every retained runtime profile gives a 127-bit per-query bound.
A joint Polygero response simulator now preserves both full responses and all
opened columns, with compatibility derived from the actual V2 compiler rows.
Concrete prefix replay and whole-block challenge counting now connect the actual
V2 frontend to V1's adaptive oracle machinery. The graded composition now uses
V1's curve, decoder-balance lemmas, rational potential compiler, and Merkle
cut-trace reduction for the actual V2 verifier. The merged two-field adaptive
bound and its authenticated two-opening reduction also check, under explicit
per-side MAC-row hypotheses for V2's `av*msg+ap` construction. The explicit
extractor returns two satisfying witnesses with equal common messages. The
zero-query experiment has the exact independent-tape coupling used in V1.
The authenticated raw-proof endpoint derives the MAC key by verifier replay
and proves `Pr[accept ∧ extraction fails] ≤ (1+N+tA)/2^117` for every pair of
query budgets. Small Merkle budgets require predictable digest guesses;
larger budgets cover the composition's startup cost. With numbered leaves,
the digest-guessing argument applies to every Merkle budget below 87.
Geometry, circuit/MAC correspondence, and balanced-sampler hypotheses remain
explicit. Compiled joint-view zero knowledge is still a component development.
Its API and axiom checks are in the default build. See the
[audit and deployment boundary](AUDIT.md) for the exact theorem chain and checks.

The [recursive Polygero development](polygero/README.md) proves witness
extraction for the transmitted recursive public-coin verifier, with failure
bound `1 − ∏ᵢ(1 − εᵢ)` from certified local errors. False-statement soundness
is derived from extraction validity and the same failure bound. It reuses
the Ligero code and tableau infrastructure.

From this directory:

```sh
lake build
```

The package uses Lean 4.31.0 and the compatible Mathlib checkout at
`../../mathlib4`, relative to `formal/`.
