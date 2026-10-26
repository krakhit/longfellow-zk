import LfzkV2.OracleSampling
import Bcs.PotentialGrinding
import polygero.Algebra.Counting.Envelope

/-! Weighted frontend roots on a shared random oracle. The cost is the total
committed weight, rather than the number of witness labels. -/

namespace LfzkV2.FiatShamir.OracleSetup

open Finset Bcs.TotalOracle RecursivePolygero RecursivePolygero.ProfileAnalysis
open scoped Classical

variable {F C Q Out Key Context Candidate : Type}
variable [Field F] [Fintype F] [DecidableEq F] [Fintype C] [Fintype Candidate]
variable [DecidableEq Q] {N L : ℕ}
variable (S : OracleSetup F C Q Out Key Context Candidate N L)

noncomputable def weightedCharge (weight : Context → Candidate → ℚ)
    (ctx : Context) (x : Q) (pref : Fin (S.points.slot x) → C) (answer : C) : ℚ :=
  ∑ candidate, weight ctx candidate *
    indicator ((S.test ctx x (S.decode ∘ pref) candidate).Bad (S.decode answer))

theorem weightedCharge_nonneg (weight : Context → Candidate → ℚ)
    (hweight : ∀ ctx candidate, 0 ≤ weight ctx candidate)
    (ctx : Context) (x : Q) (pref : Fin (S.points.slot x) → C) (answer : C) :
    0 ≤ S.weightedCharge weight ctx x pref answer := by
  exact sum_nonneg fun candidate _ => mul_nonneg (hweight ctx candidate) (indicator_nonneg _)

/-- Each label pays its own root bound. Summing its weights introduces no
cardinality factor, even when the family enumerates all polynomial tuples. -/
theorem weightedCharge_sum_le (weight : Context → Candidate → ℚ)
    (hweight : ∀ ctx candidate, 0 ≤ weight ctx candidate)
    (mass : ℚ) (hmass : ∀ ctx, ∑ candidate, weight ctx candidate ≤ mass)
    (ctx : Context) (x : Q) (pref : Fin (S.points.slot x) → C) :
    ∑ answer : C, S.weightedCharge weight ctx x pref answer ≤
      (mass * S.fiber) * S.budget x := by
  have hroot (candidate : Candidate) :
      (univ.filter fun answer : C =>
        (S.test ctx x (S.decode ∘ pref) candidate).Bad (S.decode answer)).card ≤
        S.fiber * S.budget x := by
    exact Bcs.card_decode_le S.decode S.fiber S.fiber_bound
      (S.test ctx x (S.decode ∘ pref) candidate).Bad (S.budget x)
      (((S.test ctx x (S.decode ∘ pref) candidate).card_bad_le (S.valid ctx x _ candidate)).trans
        (S.test_budget ctx x _ candidate))
  calc
    _ = ∑ candidate, weight ctx candidate *
        (univ.filter fun answer : C =>
          (S.test ctx x (S.decode ∘ pref) candidate).Bad (S.decode answer)).card := by
      unfold weightedCharge
      rw [sum_comm]
      apply sum_congr rfl
      intro candidate _
      rw [← mul_sum]
      congr 1
      simp only [indicator, sum_boole]
    _ ≤ ∑ candidate, weight ctx candidate * (S.fiber * S.budget x : ℕ) :=
      sum_le_sum fun candidate _ => mul_le_mul_of_nonneg_left
        (by exact_mod_cast hroot candidate) (hweight ctx candidate)
    _ = (∑ candidate, weight ctx candidate) * (S.fiber * S.budget x : ℕ) := (sum_mul ..).symm
    _ ≤ mass * (S.fiber * S.budget x : ℕ) :=
      mul_le_mul_of_nonneg_right (hmass ctx) (Nat.cast_nonneg _)
    _ = _ := by push_cast; ring

/-- Adaptive search over prefix points costs the same weighted root budget.
Weights may depend on the commitment context, which is fixed off the point. -/
theorem weighted_charge_mean_le [Fintype Q] [Nonempty C]
    (weight : Context → Candidate → ℚ)
    (hweight : ∀ ctx candidate, 0 ≤ weight ctx candidate)
    (mass : ℚ) (hmass0 : 0 ≤ mass) (hmass : ∀ ctx, ∑ candidate, weight ctx candidate ≤ mass)
    (maxBudget : ℕ) (hmax : ∀ x, S.budget x ≤ maxBudget)
    (slotBudget : Fin L → ℕ)
    (hslot : ∀ result i, S.budget (S.hashInput result i.val) ≤ slotBudget i) :
    mean (fun H : Q → C => ∑ x : Q, if S.grinding.Charged x H then
      S.weightedCharge weight (S.context H (S.key x)) x (S.points.chal H x) (H x) else 0) ≤
      mass * (N*maxBudget + ∑ i, slotBudget i) / Fintype.card F := by
  let scale : ℚ := mass * S.fiber
  have hscale : 0 ≤ scale := mul_nonneg hmass0 (Nat.cast_nonneg _)
  let charge := fun x (H : Q → C) c =>
    S.weightedCharge weight (S.context H (S.key x)) x (S.points.chal H x) c
  have hoff x (H H' : Q → C) (h : AgreeOff x H H') (c : C) : charge x H c = charge x H' c := by
    dsimp only [charge]
    rw [S.context_off H H' x h, ← S.points.chal_congr h]
  have hcharged x (H H' : Q → C) (h : AgreeOff x H H') :
      S.grinding.Charged x H ↔ S.grinding.Charged x H' :=
    ⟨S.grinding.charged_off h, S.grinding.charged_off h.symm⟩
  have hlocal x H : ∑ c : C, charge x H c ≤ scale * S.budget x :=
    S.weightedCharge_sum_le weight hweight mass hmass _ x _
  have htotal (H : Q → C) :
      ∑ x ∈ (univ.filter fun x => S.grinding.Charged x H), scale * S.budget x ≤
        N*(scale * maxBudget) + ∑ i, scale * slotBudget i := by
    apply S.grinding.charged_rational_budget_le
      (fun x => scale * S.budget x) (fun x => mul_nonneg hscale (Nat.cast_nonneg _))
      (scale * maxBudget) (mul_nonneg hscale (Nat.cast_nonneg _))
    · intro x
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hmax x) hscale
    · intro result i
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hslot result i) hscale
  have hsum := charged_rational_sum_le_budget S.grinding.Charged hcharged charge hoff
    (fun x => scale * S.budget x) _ hlocal htotal
  have hc : (0 : ℚ) < Fintype.card C := by exact_mod_cast Fintype.card_pos (α := C)
  have hmean : mean (fun H : Q → C => ∑ x : Q,
      if S.grinding.Charged x H then charge x H (H x) else 0) ≤
      (N*(scale * maxBudget) + ∑ i, scale * slotBudget i)/(Fintype.card C : ℚ) := by
    unfold mean
    rw [Fintype.card_fun, Nat.cast_pow, div_le_div_iff₀ (pow_pos hc _) hc]
    exact hsum
  refine hmean.trans_eq ?_
  have hf : (S.fiber : ℚ) ≠ 0 := by
    have hpos : 0 < S.fiber := by
      have hb := S.balanced
      have hp := Fintype.card_pos (α := C)
      nlinarith
    exact_mod_cast hpos.ne'
  have hcard : (Fintype.card C : ℚ) = S.fiber * (Fintype.card F : ℚ) := by
    exact_mod_cast S.balanced.symm
  rw [hcard, ← mul_sum]
  dsimp only [scale]
  push_cast
  field_simp [hf]

end LfzkV2.FiatShamir.OracleSetup
