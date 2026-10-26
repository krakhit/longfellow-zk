import polygero.FiatShamir.Potential

/-! The single-cutoff specialization of V1's terminal potential. This form
requires one system-packing certificate and keeps the numerical challenge
and query costs explicit. It also covers decoded witnesses outside the
fixed committed list. -/

namespace RecursivePolygero.NonrecursiveFS

open Finset LigeroFamily PotentialProfile ProfileAnalysis
open scoped Classical

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

theorem stepCurve_value (n threshold : ℕ) (hthreshold : 0 < threshold) (a : ℕ) :
    (stepCurve n threshold hthreshold).value a = if threshold ≤ a then 1 else 0 := by
  simp only [stepCurve, weightedStepCurve, sum_singleton]

theorem stepCurve_queryCost_le (n t threshold : ℕ) (hthreshold : 0 < threshold) :
    (stepCurve n threshold hthreshold).queryCost (fun a => hypergeometricRatio a n t) ≤
      ((threshold-1).choose t : ℚ)/n.choose t := by
  apply Finset.sup'_le
  intro a _
  rw [stepCurve_value]
  by_cases h : threshold ≤ a
  · simp only [if_pos h, sub_self, zero_mul]
    positivity
  · simp only [if_neg h, sub_zero, one_mul, hypergeometricRatio]
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast Nat.choose_le_choose t (by omega : a ≤ threshold-1)) (by positivity)

/-- One fixed threshold suffices for the challenge mean. The bound is
uniform in the statement and committed oracle. -/
theorem step_potential_mean_le (I : Instance F) (p : ProfileParameters I)
    (threshold L : ℕ) (hthreshold : 0 < threshold) (hlarge : p.largeSize ≤ threshold)
    (hpacking : CodingTheory.UniformFamilyBound I.n threshold p.overlapSize L)
    (σ : I.layer.Statement) (W : I.layer.Oracle) :
    mean (fun coin : I.layer.Coin =>
      (stepCurve I.n threshold hthreshold).value (maxFailureAgreement I σ W coin)) ≤
      p.rankError + L/(Nat.card F : ℚ) := by
  have h := maxFailureAgreement_tail_le_of_uniformFamilyBound I p σ W threshold L hlarge hpacking
  apply le_trans (le_of_eq ?_) h
  congr 1
  funext coin
  rw [stepCurve_value]
  split_ifs with ha <;> simp [indicator, ha]

/-- Explicit two-role terminal costs, using V1's step curve and exact
decoder fiber factors. `cutoff` belongs to the committed witness list;
`threshold` belongs to the response-failure capacity list. -/
noncomputable def stepTerminalPotential (I : Instance F) (p : ProfileParameters I)
    (cutoff threshold L : ℕ) (hthreshold : 0 < threshold) (hlarge : p.largeSize ≤ threshold)
    (hpacking : CodingTheory.UniformFamilyBound I.n threshold p.overlapSize L)
    {C : Type} [Fintype C] (decodeCoin : C → I.layer.Coin) (decodeQuery : C → I.layer.Query)
    (kCoin kQuery : ℕ)
    (hcoin : ∀ coin, (univ.filter fun c : C => decodeCoin c = coin).card ≤ kCoin)
    (hquery : ∀ query, (univ.filter fun c : C => decodeQuery c = query).card ≤ kQuery) :
    TerminalPotential I cutoff decodeCoin decodeQuery where
  weight σ W coin := (stepCurve I.n threshold hthreshold).value (maxFailureAgreement I σ W coin)
  nonneg σ W coin := (stepCurve I.n threshold hthreshold).nonneg _ (maxFailureAgreement_le I σ W coin)
  le_one σ W coin := (stepCurve I.n threshold hthreshold).le_one _ (maxFailureAgreement_le I σ W coin)
  challengeBudget := kCoin * Fintype.card I.layer.Coin * (p.rankError + L/(Nat.card F : ℚ))
  queryBudget := kQuery * Fintype.card I.layer.Query *
    max (((threshold-1).choose I.t : ℚ)/I.n.choose I.t)
      (((cutoff+I.s-1).choose I.t : ℚ)/I.n.choose I.t)
  challengeBudget_nonneg := by unfold ProfileParameters.rankError; positivity
  queryBudget_nonneg := by positivity
  challenge_le σ W := LfzkV1.ZkPotentialBalance.decoded_mean_le decodeCoin
    (fun coin => (stepCurve I.n threshold hthreshold).value (maxFailureAgreement I σ W coin))
    (fun coin => (stepCurve I.n threshold hthreshold).nonneg _ (maxFailureAgreement_le I σ W coin))
    kCoin hcoin _ (step_potential_mean_le I p threshold L hthreshold hlarge hpacking σ W)
  query_le σ W hnosat coin response := by
    have h := query_hash_charge_le_of_noSat I σ W (stepCurve I.n threshold hthreshold) cutoff
      hnosat coin response decodeQuery kQuery hquery
    exact h.trans (mul_le_mul_of_nonneg_left
      (max_le_max (stepCurve_queryCost_le I.n I.t threshold hthreshold) le_rfl) (by positivity))

end RecursivePolygero.NonrecursiveFS
