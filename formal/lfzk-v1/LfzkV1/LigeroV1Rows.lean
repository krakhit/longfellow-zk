import LfzkV1.LigeroV1Rbr
import examples.Ligero.Longfellow.ProfiledExtraction

/-!
# Certified round-by-round rows for Ligero V1

A `Row` is one of `formal/ligero`'s `Certificate` records — the geometry `(n, k, d, openings)`,
the analysis parameters `(e, g, m)` and the field — together with the two doom thresholds the
round-by-round statement needs.  `Row.Valid` is decidable, so a row is checked by `native_decide`
exactly as `OptimizedIOPCertificates` checks its flat certificates, and `Row.rbr_soundness` is
`Ligero.V1.ligerov1_roundByRound_mask_profiled` at the row, with every hypothesis discharged from
`Row.Valid` the way `Result.v1_strategy` discharges the flat theorem's.

The three numbers a row quotes are the two per-slot budgets of the Ligero layer and the lift-list
factor that multiplies both:

* `cover` — from a doomed challenge, the fraction of query sets the verifier accepts;
* `fail + arith` — the fraction of challenges that escape doom (the failure profile's tail above
  `failureThreshold` over `formal/ligero`'s optimized denominator, plus the unchecked arithmetic
  profile's tail above `arithmeticThreshold`);
* `listBound` — the size of the oracle's lift list, paid once by the claim chain.

`epsRbr := listBound · (cover + fail + arith)`, and `Row.Valid` records `epsRbr ≤ 2^-targetBits`,
with `targetBits` the **round-by-round** target of this row (the `Certificate.targetBits` field is
reused for it; these certificates are not the flat ones, so no flat theorem reads it).

The v7 rows in `LigeroV1RowsV7` are produced by `lfzk-v1/scripts/v7_rows.py`, which uses the
definitions transcribed in `rbr_v1_rows.py`; `--check` re-derives those committed rows. `LigeroV1RowsHahn`
additionally supplies a row with a Hahn/Delsarte mask certificate. The searches are untrusted
optimizers: nothing is a result until `Row.Valid` is checked here.
-/

namespace LfzkV1.LigeroV1Rows

open LigeroFamily CodingTheory
open Ligero.Examples.Grid
open Ligero.Examples.Grid.LongfellowIOP (certificateCode certificateCodeFacts)
open Ligero.Examples.Grid.LongfellowProfiledExtraction (Result)

deriving instance DecidableEq for Certificate

/-- The order of P-256's base field, `2^256 - 2^224 + 2^192 + 2^96 - 1`. -/
def p256Order : ℕ :=
  115792089210356248762697446949407573530086143415290314195533631308867097853951

/-- A round-by-round row: a certificate plus the two doom thresholds. -/
structure Row where
  certificate : Certificate
  failureThreshold : ℕ
  arithmeticThreshold : ℕ
deriving DecidableEq

namespace Row

variable (row : Row)

abbrev n : ℕ := row.certificate.n
abbrev k : ℕ := row.certificate.k
abbrev d : ℕ := row.certificate.d
abbrev e : ℕ := row.certificate.e
abbrev g : ℕ := row.certificate.g
abbrev m : ℕ := row.certificate.m
abbrev openings : ℕ := row.certificate.openings
/-- The round-by-round target of the row. -/
abbrev targetBits : ℕ := row.certificate.targetBits
abbrev fieldSize : ℕ := row.certificate.fieldSize
abbrev fieldOrder : ℕ := row.certificate.fieldOrder
/-- The lift-list bound `Certificate.listSize`: the Johnson count
`InterleavedJohnson.listBound n d (e + g)`, capped by integer packing. -/
abbrev listBound : ℕ := row.certificate.listSize
/-- V1's Johnson threshold, `⌊√(n(2k−1))⌋ + 1`. -/
abbrev johnsonThreshold : ℕ := row.certificate.v1Threshold

/-- The row as one of `formal/ligero`'s V1 triples-route results. -/
def result : Result := { variant := .v1, route := .triples, certificate := row.certificate }

/-- The failure profile at field size `q`: `formal/ligero`'s optimized integrated profile at the
row's outer line bound `m − 1` and its agreement-local line bounds. -/
def failureProfileAt (q : ℕ) : AgreementProfile row.n :=
  SchemeSelectedMCA.selectedMCAOptimizedIntegratedFailureProfile q row.n row.e row.g row.d
    row.certificate.lineBound row.certificate.integratedLocalLineBound

/-- The unchecked arithmetic profile of V1's direct response masks, using the certificate's
Johnson range and any certified Hahn/Delsarte extension below it. -/
def arithProfile : AgreementProfile row.n :=
  maskAgreementProfile row.fieldSize row.n row.listBound row.certificate.maskStart
    row.certificate.maskBound

/-- Existing rows with no mask extension retain exactly their Johnson arithmetic profile. -/
theorem arithProfile_eq_johnson (h : row.certificate.maskThreshold = 0) :
    row.arithProfile = uncheckedAgreementProfile row.fieldSize row.n (2 * row.k - 1)
      row.listBound row.johnsonThreshold := by
  unfold arithProfile maskAgreementProfile uncheckedAgreementProfile
  congr 1
  funext a
  simp only [Certificate.maskStart, h, ↓reduceIte, Certificate.maskBound]
  by_cases hn : row.n < a
  · simp [hn]
  · by_cases ht : a < row.johnsonThreshold
    · simp [hn, ht]
    · simp [hn, ht, show row.certificate.v1Threshold ≤ a from Nat.le_of_not_gt ht]

/-- The column count a doomed challenge's accepting queries must land in. -/
def queryCover : ℕ :=
  max row.failureThreshold
    (max (row.n - row.e - 1) (min row.n (row.g + row.arithmeticThreshold)))

/-- The query round's budget, as a density. -/
def cover : ℚ := hypergeometricRatio row.queryCover row.n row.openings

/-- The failure profile's tail above the failure threshold, over the optimized denominator. -/
def fail : ℚ :=
  ((row.failureProfileAt row.fieldSize).labelsAtLeast (row.failureThreshold + 1) : ℚ) /
    (row.certificate.optimizedFailureDenominator : ℚ)

/-- The arithmetic profile's tail above the arithmetic threshold. -/
def arith : ℚ :=
  (row.arithProfile.labelsAtLeast (row.arithmeticThreshold + 1) : ℚ) / (row.fieldSize : ℚ)

/-- The row's round-by-round error: the two slots' budgets, times the lift-list factor. -/
def epsRbr : ℚ := (row.listBound : ℚ) * (row.cover + row.fail + row.arith)

/-- The row-side checks.  The first nine are `Result.ParametersValid`'s content on the triples
route, in the decidable form `Certificate.conditions_of_checked` consumes; the rest are the
threshold ranges, the target, and `Certificate.maskValid` (V1's mask-certificate check). -/
def Valid : Prop :=
  0 < row.k ∧ row.k ≤ row.n ∧ row.d = row.n - row.k + 1 ∧ 2 * row.k ≤ row.n ∧
    SelectedMCA.DirectCliqueCondition row.n row.e row.g row.d row.m ∧
    3 * row.g < row.d - row.e ∧ row.g + 1 < row.fieldSize ∧
    0 < InterleavedJohnson.denominator row.n row.d (row.e + row.g) ∧
    row.certificate.integratedLocalValidBool = true ∧
    row.failureThreshold + 1 ≤ row.n ∧ row.arithmeticThreshold + 1 ≤ row.n ∧
    row.openings ≤ row.n ∧
    row.epsRbr ≤ (1 : ℚ) / 2 ^ row.targetBits ∧ row.certificate.maskValid = true

instance : Decidable row.Valid := by unfold Valid; infer_instance

/-- `Row.Valid` as a `Bool`, for `native_decide` over a list of rows. -/
def validBool : Bool := decide row.Valid

/-- The recorded target is the row's exact integer bit level. -/
def Sharp : Prop := ¬ row.epsRbr ≤ (1 : ℚ) / 2 ^ (row.targetBits + 1)

instance : Decidable row.Sharp := by unfold Sharp; infer_instance

def sharpBool : Bool := decide row.Sharp

variable {row}

theorem kpos (h : row.Valid) : 0 < row.k := h.1
theorem k_le (h : row.Valid) : row.k ≤ row.n := h.2.1
theorem distance_eq (h : row.Valid) : row.d = row.n - row.k + 1 := h.2.2.1
theorem response_le (h : row.Valid) : 2 * row.k ≤ row.n := h.2.2.2.1
theorem clique (h : row.Valid) :
    SelectedMCA.DirectCliqueCondition row.n row.e row.g row.d row.m := h.2.2.2.2.1
theorem three_radius (h : row.Valid) : 3 * row.g < row.d - row.e := h.2.2.2.2.2.1
theorem field_large (h : row.Valid) : row.g + 1 < row.fieldSize := h.2.2.2.2.2.2.1
theorem denominator_pos (h : row.Valid) :
    0 < InterleavedJohnson.denominator row.n row.d (row.e + row.g) := h.2.2.2.2.2.2.2.1
theorem localValid (h : row.Valid) : row.certificate.integratedLocalValidBool = true :=
  h.2.2.2.2.2.2.2.2.1
theorem failureThreshold_le (h : row.Valid) : row.failureThreshold + 1 ≤ row.n :=
  h.2.2.2.2.2.2.2.2.2.1
theorem arithmeticThreshold_le (h : row.Valid) : row.arithmeticThreshold + 1 ≤ row.n :=
  h.2.2.2.2.2.2.2.2.2.2.1
theorem openings_le (h : row.Valid) : row.openings ≤ row.n := h.2.2.2.2.2.2.2.2.2.2.2.1
theorem eps_le_target (h : row.Valid) : row.epsRbr ≤ (1 : ℚ) / 2 ^ row.targetBits :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem maskValid (h : row.Valid) : row.certificate.maskValid = true :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- A valid row's certificate meets `formal/ligero`'s own parameter validity on the triples
route. -/
theorem parametersValid (h : row.Valid) : row.result.ParametersValid := by
  simp only [Result.ParametersValid, Row.result]
  exact ⟨kpos h, k_le h, distance_eq h, response_le h, by simpa using maskValid h,
    row.certificate.conditions_of_checked (clique h) (three_radius h) (field_large h)
      (denominator_pos h) (localValid h)⟩

theorem codeFits (h : row.Valid) {w : ℕ} (hkrow : row.openings + w = row.k) :
    row.openings + w ≤ row.n := by
  have := k_le h
  omega

/-- The row's Reed–Solomon multiplicative code over a domain `D`. -/
noncomputable abbrev code (h : row.Valid) {F : Type*} [Field F] [DecidableEq F] {w : ℕ}
    (D : ReedSolomon.Domain F row.openings w row.n) (hkrow : row.openings + w = row.k) :
    MultiplicativeCode F row.openings w row.n :=
  certificateCode row.certificate D (codeFits h hkrow)

theorem rsFacts (h : row.Valid) {F : Type*} [Field F] [DecidableEq F] {w : ℕ}
    (D : ReedSolomon.Domain F row.openings w row.n) (hkrow : row.openings + w = row.k) :
    (row.code h D hkrow).k = row.k ∧
    HasMinimumDistanceAtLeast (row.code h D hkrow).baseCode row.d ∧
    Nonempty (JBAgreement.RSPresentation row.n row.k (row.code h D hkrow).baseCode) :=
  certificateCodeFacts row.certificate (kpos h) (distance_eq h) hkrow D (codeFits h hkrow)

/-- The committed oracle's lift list at radius `e + g` has at most `listBound` members
(`Certificate.listFamily`: the Johnson count, refined by integer packing). -/
theorem liftList_card_le (h : row.Valid) {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {w nw nq : ℕ}
    (D : ReedSolomon.Domain F row.openings w row.n) (hkrow : row.openings + w = row.k)
    (oracle : Ligero.V1.Oracle F nw nq row.n 1) :
    (Finset.univ : Finset (SchemeLiftCandidate (row.code h D hkrow) oracle
      (row.e + row.g))).card ≤ row.listBound := by
  obtain ⟨-, hmin, -⟩ := rsFacts h D hkrow
  have hradius : row.e + row.g < row.d := by have := three_radius h; omega
  exact SchemeLiftCandidate.univ_card_le_uniformFamilyBound _ oracle hmin hradius
    (row.certificate.listFamily hradius hmin.distance_le_length (denominator_pos h))

/-- **The round-by-round Ligero V1 facts at a certified row.**  For a false statement, there is a
classifier of the V1 verifier (one repetition, at the row's code) such that a doomed challenge's
accepting queries have density at most `row.cover`, the escaping challenges have density at most
`row.fail + row.arith`, and every undoomed challenge escapes. -/
theorem rbr_soundness (h : row.Valid)
    {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations] {w nw nq : ℕ}
    (hrows : CoreRowsNonempty nw nq)
    (hfield : Fintype.card F = row.fieldSize)
    (D : ReedSolomon.Domain F row.openings w row.n)
    (hkrow : row.openings + w = row.k)
    (statement : ConstraintSystem F nw nq w Equations)
    (prover : IPCPProver
      (ConstraintSystem F nw nq w Equations)
      (Ligero.V1.Oracle F nw nq row.n 1)
      (Ligero.V1.Challenge F nw nq 1 Equations)
      (Response F row.openings w row.n 1))
    (hfalse : ¬ statement.Language) :
    ∃ classifier : PolicyDoublyProfiledSoundnessClassifier
        (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq)
          (repetitions := 1) (row.code h D hkrow) Ligero.V1.scheme)
        (prover.commit statement) statement
        (fun challenge ↦ prover.respond statement (prover.commit statement) challenge)
        (row.failureProfileAt (Fintype.card F))
        (maskAgreementProfile (Fintype.card F) row.n row.listBound row.certificate.maskStart
          row.certificate.maskBound)
        (Fintype.card F)
        (SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator (Fintype.card F) row.g)
        row.e row.g,
      (∀ challenge, classifier.ProfiledDoomedAfter
          row.failureThreshold row.arithmeticThreshold challenge →
        ((classifier.acceptingQueries challenge).card : ℚ) /
            (row.n.choose row.openings) ≤ row.cover)
      ∧ ((classifier.profiledEscaping
            row.failureThreshold row.arithmeticThreshold).card : ℚ) /
            Fintype.card (Ligero.V1.Challenge F nw nq 1 Equations) ≤ row.fail + row.arith
      ∧ (∀ challenge, ¬ classifier.ProfiledDoomedAfter
            row.failureThreshold row.arithmeticThreshold challenge →
          challenge ∈ classifier.profiledEscaping
            row.failureThreshold row.arithmeticThreshold) := by
  obtain ⟨hk, hmin, ⟨P⟩⟩ := rsFacts h D hkrow
  have hcond := row.result.lineConditions (parametersValid h) hfield hmin P
  have mask := V1Certificate.v1MaskRange row.certificate (kpos h) (response_le h)
    (maskValid h) (row.code h D hkrow) hk
  obtain ⟨classifier, hq, hesc, hmem⟩ :=
    Ligero.V1.ligerov1_roundByRound_mask_profiled hrows (row.code h D hkrow) statement prover
      (NoDecodedSolution.of_not_language hfalse) hmin hcond (liftList_card_le h D hkrow _) mask
      row.failureThreshold row.arithmeticThreshold
      (failureThreshold_le h) (arithmeticThreshold_le h)
  refine ⟨classifier, fun challenge hdoom ↦ hq challenge hdoom, ?_, hmem⟩
  refine hesc.trans (le_of_eq ?_)
  -- Only the field size and the code's dimension are propositional; the rest is unfolding.
  simp only [hfield]
  rfl

end Row

end LfzkV1.LigeroV1Rows
