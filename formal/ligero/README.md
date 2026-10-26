# Ligero V1 extraction and soundness

This development proves scalar Ligero IOP extraction and false-statement
soundness. It includes exact v7 component certificates and separate local
challenge/query count certificates.

Version 8 uses Polygero; its certificates are in
[`parameters/polygero`](../parameters/polygero).

## Certified v7 bounds

At 132 distinct column openings, the IOP error is at most `2^-s`, with the
following integer exponents:

| Component | V1 |
|---|---:|
| v7 signature (all attribute counts) | 127 |
| v7 hash (1–4 attributes) | 125 |

The V1 entries use Hahn/Delsarte certificates for the unchecked-mask list
below the Johnson threshold. These certificates improve the previous V1
signature/hash bounds from 125/124 to 127/125 bits.

[OptimizedIOPCertificates](examples/Ligero/Longfellow/OptimizedIOPCertificates.lean)
checks all geometry, field-order, clique/Johnson, Hahn/Delsarte, and
rational-budget premises.
The [IOP catalog](examples/Ligero/Longfellow/optimized-iop-certified-results.json)
records exact parameters and theorem names.

Each signature geometry covers one through four attributes. Hash components
have separate records for each attribute count. The signature field is the
P-256 base field; the hash field has order `2^128`.

## Major proved results

| Result | Main theorem or interface | Source |
|---|---|---|
| Reed–Solomon minimum distance and the concrete multiplicative-code instance | `ReedSolomon.evaluation_code_minimum_distance`, `LongfellowIOP.certificateCodeFacts` | [Distance](ReedSolomon/Distance.lean), [IOPParameters](examples/Ligero/Longfellow/IOPParameters.lean) |
| Selected-MCA proximity bounds from affine triple counting and punctured globalization | `SelectedMCA.directionallyNonliftableParameters_card_le_direct`, `closeCombinationChallengesOn_card_le_of_direction_far` | [DirectLineExtraction](SelectedMCA/DirectLineExtraction.lean), [Punctured](SelectedMCA/Punctured.lean) |
| Reed–Solomon JB agreement with the η³ threshold, including checked inverse-η parameters | `JBAgreement.lineFailureBound_of_johnsonConditions`, `lineFailureBound_of_inverseEtaConditions` | [Certificate](JBAgreement/Certificate.lean), [InverseEtaCertificate](JBAgreement/InverseEtaCertificate.lean) |
| Delsarte LP bound using Hahn kernels for uniform intersection families (Johnson is degree one), with decidable integer certificates | `CodingTheory.HahnDelsarte.card_le_of_delsarte`, `hahnKernel_gram_nonneg`, `uniformFamilyBound_of_certificate` | [HahnDelsarte](CodingTheory/ListDecoding/HahnDelsarte.lean), [UniformFamily](CodingTheory/ListDecoding/UniformFamily.lean) |
| Integer one- and two-candidate packing bounds, and an independent packing interface for the shared decoded-witness list | `CodingTheory.uniformFamilyBound_one_of_two_mul_gt`, `uniformFamilyBound_two_of_three_mul_gt`, `SchemeLiftCandidate.univ_card_le_uniformFamilyBound` | [UniformFamily](CodingTheory/ListDecoding/UniformFamily.lean), [SchemeFixedLiftList](LigeroFamily/Soundness/SchemeFixedLiftList.lean) |
| V1 unchecked-mask list bounded by any uniform-family bound (Johnson above, Hahn/Delsarte below the Johnson threshold) | `Ligero.V1.responseWordsAgreeingAtLeast_card_le_of_bound`, `Ligero.V1.V1MaskRange` | [MaskAgreement](Ligero/V1/Soundness/MaskAgreement.lean), [V1Profile](Ligero/V1/Soundness/V1Profile.lean), [HahnMaskCertificates](examples/Ligero/Longfellow/HahnMaskCertificates.lean) |
| Validity and agreement guarantees for the response-assisted extractor | `LigeroFamily.ScalarGapExtraction.extract_valid`, `extract_agreement_errors` | [ScalarGapExtraction](LigeroFamily/Soundness/ScalarGapExtraction.lean) |
| Scalar IOP extraction for V1 | `Ligero.V1.scalarGap_extraction_failure`, `scalarGap_iop_extraction_failure` | [V1](Ligero/V1/ScalarGapExtraction.lean) |
| Refined IOP extraction with a single response-uniform envelope | `Ligero.V1.scalarGap_profiled_extraction_failure`, `ScalarGapExtraction.profiledUniformEnvelope_mean_of_strategies` | [V1](Ligero/V1/ScalarGapProfiled.lean), [Shared proof](LigeroFamily/Soundness/ScalarGapProfiled.lean) |
| False-statement soundness from extractor validity | `ScalarGapExtraction.Certificate.false_statement`, `CertifiedResult.v1_interactive` | [ScalarGapExtraction](LigeroFamily/Soundness/ScalarGapExtraction.lean), [ProfiledExtraction](examples/Ligero/Longfellow/ProfiledExtraction.lean) |
| Merkle prefix binding and consistency of accepted openings | `Merkle.MH.PrefixBindingGame.bad_ratio_le`, `PrefixBindingFamily.boundMessage_game_eq` | [PrefixBinding](../merkle/Merkle/PrefixBinding.lean) |
| Exact IOP instances and local count certificates for v7 geometries | `Optimized.v7*` extraction and interactive endpoints; `CountCertificate` | [IOP certificates](examples/Ligero/Longfellow/OptimizedIOPCertificates.lean), [count certificates](examples/Ligero/Longfellow/AdaptiveOptimizedCertificates.lean) |

Example theorem names in the table abbreviate the shared namespace
`Ligero.Examples.Grid`. `CertifiedResult` is in
`Ligero.Examples.Grid.LongfellowProfiledExtraction`; component endpoints are
in its `Optimized` namespace.

## Protocol and extraction

V1 uses the original unchecked arithmetic masks and scalar batching.

For V1, the arithmetic profile charges probability one only below the mask
threshold. Above it, the response-code words agreeing with an unchecked mask on
at least `a` columns form `a`-subsets meeting pairwise in at most `2k-1`
columns, so any uniform-family bound limits them. The Johnson count gives a
finite bound only for `a² > n(2k-1)`. One Hahn/Delsarte certificate of degree
at least nine extends the bound below that threshold. Its cutoff is
selected against the complete extraction budget. By size monotonicity it
covers every level up to the Johnson threshold. Each certificate is an
integer nonnegative combination of Hahn kernels, checked against every
realizable overlap by the proved Gram-kernel interface. The polynomial
construction used to generate candidates is not an assumption of the proof.

The extractor takes the committed oracle, statement, challenge, and response.
A successful extraction returns a witness satisfying the original constraints.
The IOP extraction-failure event is verifier acceptance together with the
extractor returning `none`. Its bound holds for arbitrary statements and
prover response strategies; false-statement soundness follows by validity.

In the IOP experiment, the oracle is committed before the uniform batching
challenge, and the response precedes the independent uniform fixed-size
column query. The refined proof supplies one envelope fixed from the oracle
and statement that bounds every response's query acceptance probability.
Its challenge mean supplies the error coefficient used in the Longfellow analysis.

## Local count certificates

The local V1 challenge/query counts come from its profiled agreement
proofs, uniformly over the response fixed before the query draw.
The count certificates below are checked arithmetic statements for those
local budgets.

Exact v7 profile thresholds give the following **per-round count**
exponents. For each entry, both the escape-challenge fraction and the
doomed-challenge accepting-query fraction are at most `2^-b`. The optimized
hash geometries and their validity and count proofs are checked in
[AdaptiveHashCertificates](examples/Ligero/Longfellow/AdaptiveHashCertificates.lean).
Here "optimized" records improved certified choices; the development does not
prove that no other parameters or certificates give a stronger bound.
[AdaptiveCountCertificates](examples/Ligero/Longfellow/AdaptiveCountCertificates.lean)
supplies the integer counts and V1 escape-budget adapters.
The V1 signature rows are in
[AdaptiveSignatureCertificates](examples/Ligero/Longfellow/AdaptiveSignatureCertificates.lean).
They use separate, checked
[Hahn mask certificates](examples/Ligero/Longfellow/HahnMaskFSSignature.lean)
with the Johnson line geometry; their verifier and mask policy remain V1.

| Geometry | V1 `b` |
|---|---:|
| v7 signature | 132 |
| v7 hashes 1–4 | 117 |

The exact integer escape count has a rounding cost strictly below one
challenge point, as proved by `CountCertificate.escape_ratio_lt`.

## Organization and checking

The common protocol and extraction proofs are in `LigeroFamily`. The V1
bridge is in `Ligero/V1`.
[FiniteResponse](LigeroFamily/Protocol/FiniteResponse.lean) supplies finite
response instances, while
[FirstOccurrenceTrace](../bcs/Bcs/FirstOccurrenceTrace.lean) supplies query-slot
bookkeeping. [Certificate](examples/Ligero/Certificate.lean) contains the shared
example arithmetic. `Ligero.API` exposes the extraction surface, and
`Ligero.APITest` checks it together with representative component endpoints.

From `formal/`, build the ordinary Longfellow development with:

```sh
lake build LfzkV1
```

The improved Ligero local-count certificates, including the V1 signature Hahn
checks above, are included in the default build. `LigeroLocalCounts` also builds
them on their own. Exact integer polynomial checks replace the former radius
range checks, and the public certificate theorems reuse the checked results.
The aggregate
[AdaptiveOptimizedCertificates](examples/Ligero/Longfellow/AdaptiveOptimizedCertificates.lean)
module preserves the existing import path. Hash-only users can build
`examples.Ligero.Longfellow.AdaptiveHashCertificates` without importing the
signature certificate.

```sh
scripts/build.sh LigeroLocalCounts
```

To regenerate the polynomial proposals from the committed certificate coefficients, run:

```sh
cargo run --manifest-path parameters/hahn/generator/Cargo.toml -- .
```

Lean checks every generated Hahn identity, sign and list bound in its kernel.
The surrounding protocol budget records retain their native arithmetic checks.
