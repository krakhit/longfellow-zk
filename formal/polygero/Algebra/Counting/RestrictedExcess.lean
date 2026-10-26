import polygero.Algebra.Counting.SystemExceptions

/-! A restricted excess bound controls the number and raw mass of high entries. -/
namespace RecursivePolygero.RestrictedExcess
open Finset
open scoped Classical

/-- Fewer than `q` entries can exceed the raised baseline. -/
theorem above_threshold_card_lt {D : Type*} [Fintype D]
    (a : D → ℚ) (q : ℕ) (hq : 0 < q) (theta epsilon : ℚ)
    (hgap : 1-theta ≤ (q : ℚ)*(epsilon-theta))
    (hbound : ∀ T : Finset D, T.card ≤ q →
      ∑ d ∈ T, max 0 (a d-theta) ≤ 1-theta) :
    (univ.filter fun d => epsilon < a d).card < q := by
  classical
  let T := univ.filter fun d => epsilon < a d
  change T.card < q
  by_contra hn
  obtain ⟨S, hST, hS⟩ := exists_subset_card_eq (show q ≤ T.card from by omega)
  have hne : S.Nonempty := card_pos.mp (by omega)
  have hlt : ∑ _d ∈ S, (epsilon-theta) < ∑ d ∈ S, max 0 (a d-theta) := by
    apply sum_lt_sum_of_nonempty hne
    intro d hd
    have ha := (mem_filter.mp (hST hd)).2
    exact (by linarith : epsilon-theta < a d-theta).trans_le (le_max_right _ _)
  simp only [sum_const, nsmul_eq_mul, hS] at hlt
  have hb := hbound S hS.le
  linarith

/-- Raw mass above the raised threshold, using the same restricted excess
certificate. This is useful when parent and child queries have separate roles. -/
theorem high_mass_of_restricted {D : Type*} [Fintype D]
    (a : D → ℚ) (q : ℕ) (hq : 0 < q) (theta epsilon : ℚ)
    (ht0 : 0 ≤ theta) (hte : theta ≤ epsilon)
    (hgap : 1-theta ≤ (q : ℚ)*(epsilon-theta))
    (hbound : ∀ T : Finset D, T.card ≤ q →
      ∑ d ∈ T, max 0 (a d-theta) ≤ 1-theta) :
    ∑ d ∈ univ.filter (fun d => epsilon < a d), a d ≤
      1-theta+((q : ℚ)-1)*theta := by
  classical
  let T := univ.filter fun d => epsilon < a d
  have hc : T.card < q := above_threshold_card_lt a q hq theta epsilon hgap hbound
  have hboundT := hbound T hc.le
  have heq : ∑ d ∈ T, max 0 (a d-theta) = (∑ d ∈ T, a d)-T.card*theta := by
    calc
      _ = ∑ d ∈ T, (a d-theta) := sum_congr rfl (fun d hd =>
        max_eq_right (by have := (mem_filter.mp hd).2; linarith))
      _ = _ := by simp [sum_sub_distrib]
  have hct : (T.card : ℚ) ≤ (q : ℚ)-1 := by
    have h : (T.card : ℚ)+1 ≤ (q : ℚ) := by exact_mod_cast (show T.card+1 ≤ q by omega)
    linarith
  have hm := mul_le_mul_of_nonneg_right hct ht0
  change ∑ d ∈ T, a d ≤ _
  rw [heq] at hboundT
  linarith

end RecursivePolygero.RestrictedExcess
