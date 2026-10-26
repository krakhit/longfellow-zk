import polygero.Algebra.ProximityGap

/-! Increasing the analysis degree preserves the rank-defect bound.
The sampled protocol challenge degree is unchanged. -/
namespace RecursivePolygero.ExtendedGap
open Polynomial Finset Submodule RecursivePolygero.ProximityGap
open RecursivePolygero.Local RecursivePolygero.Local.Shift
variable {F : Type*} [Field F] {n m : ℕ}

section Growth
variable {M : Type*} [AddCommGroup M] [Module F M] [FiniteDimensional F M]
omit [FiniteDimensional F M] in
theorem growthChain_add (T : M →ₗ[F] M) (U : Submodule F M) (a b : ℕ) :
    growthChain T U (a+b) = growthChain T (growthChain T U a) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change grow T (growthChain T U (a+b)) = _
    rw [ih]
    rfl

/-- Once one shift adds at most one dimension, every later shift does too. -/
theorem growthChain_finrank_le (T : M →ₗ[F] M) (U : Submodule F M)
    (hg : Module.finrank F (grow T U) ≤ Module.finrank F U + 1) (j : ℕ) :
    Module.finrank F (growthChain T U j) ≤ Module.finrank F U + j := by
  have hstep (i : ℕ) : Module.finrank F (growthChain T U (i+1)) ≤
      Module.finrank F (growthChain T U i) + 1 := by
    induction i with
    | zero => exact hg
    | succ i ih =>
      have h := quotient_growth_bound T (growthChain T U i)
        (growthChain T U (i+1)) le_sup_left le_sup_right
      change Module.finrank F (growthChain T U (i+1+1)) + _ ≤ _ at h
      omega
  induction j with
  | zero => exact le_rfl
  | succ j ih => have := hstep j; omega

end Growth

/-- Increasing the polynomial coefficient degree preserves the defect bound.
This changes only an analysis space, not the sampled protocol challenge. -/
theorem polynomialSpace_finrank_le_of_le_degree (x : Fin n → F)
    (hx : Function.Injective x) (W : Fin m → (Fin n → F))
    (k s δ b : ℕ) (hk : 1 ≤ k) (hδ : δ ≤ s)
    (hN : k+s+δ < n) (hd : Module.finrank F (polynomialSpace x W k s) = k+s+δ)
    (hsb : s ≤ b) :
    Module.finrank F (polynomialSpace x W k b) ≤ k+b+δ := by
  let C : Codes.RSCode F n (k+s) := ⟨x, hx, by omega⟩
  have he : polynomialSpace x W k s = receivedSpace x W k s :=
    aggregateSpace_eq_receivedSpace C W hk
  have hg := polynomialSpace_slow_growth x hx W k s δ hk hδ hN hd
  have hb := growthChain_finrank_le (shift x) (polynomialSpace x W k s) hg (b-s)
  by_cases hbn : k+b ≤ n
  · let CB : Codes.RSCode F n (k+b) := ⟨x, hx, hbn⟩
    have heb : polynomialSpace x W k b = receivedSpace x W k b :=
      aggregateSpace_eq_receivedSpace CB W hk
    have hext : receivedSpace x W k b =
        growthChain (shift x) (polynomialSpace x W k s) (b-s) := by
      change growthChain (shift x) (seed x W k) b = _
      rw [show b = s+(b-s) by omega, growthChain_add]
      rw [← receivedSpace, ← he]
      congr 1
      omega
    rw [heb, hext]
    rw [hd] at hb
    omega
  · have h := Submodule.finrank_le (polynomialSpace x W k b)
    simp only [Module.finrank_fin_fun] at h
    omega

open scoped Classical in
/-- A low-defect polynomial space admits at most one sufficiently agreeing
response even when the fixed row coefficients have larger degree. -/
theorem response_eq_of_large_agreement (x : Fin n → F) (hx : Function.Injective x)
    (W : Fin m → (Fin n → F)) (k s δ b : ℕ) (hk : 1 ≤ k) (hδ : δ ≤ s)
    (hN : k+s+δ < n) (hd : Module.finrank F (polynomialSpace x W k s) = k+s+δ)
    (hsb : s ≤ b) (B : Fin m → degreeLT F (b+1))
    (p p' : degreeLT F (k+b))
    (hp : k+b+δ ≤ (univ.filter fun j => batch x W B j = p.1.eval (x j)).card)
    (hp' : k+b+δ ≤ (univ.filter fun j => batch x W B j = p'.1.eval (x j)).card) :
    p = p' := by
  classical
  have hcount : (univ.filter fun j => batch x W B j = p.1.eval (x j)).card ≤ n := by
    simpa using (card_le_univ (univ.filter fun j => batch x W B j = p.1.eval (x j)))
  have hnb : k+b+δ ≤ n := hp.trans hcount
  apply Subtype.ext
  by_cases heq : k+b+δ = n
  · have hall (z : degreeLT F (k+b))
        (hz : k+b+δ ≤ (univ.filter fun j => batch x W B j = z.1.eval (x j)).card) :
        ∀ j, batch x W B j = z.1.eval (x j) := by
      have he : (univ.filter fun j => batch x W B j = z.1.eval (x j)) = univ :=
        eq_of_subset_of_card_le (subset_univ _) (by simpa only [card_univ,
          Fintype.card_fin, ← heq] using hz)
      intro j
      have hj : j ∈ (univ.filter fun j => batch x W B j = z.1.eval (x j)) := by
        rw [he]
        exact mem_univ j
      exact (mem_filter.mp hj).2
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq univ hx.injOn
    · exact (mem_degreeLT.mp p.2).trans_le (by
        exact_mod_cast (show k+b ≤ (univ : Finset (Fin n)).card from by
          simpa using (show k+b ≤ n from by omega)))
    · exact (mem_degreeLT.mp p'.2).trans_le (by
        exact_mod_cast (show k+b ≤ (univ : Finset (Fin n)).card from by
          simpa using (show k+b ≤ n from by omega)))
    · intro j _; exact (hall p hp j).symm.trans (hall p' hp' j)
  · let db := Module.finrank F (polynomialSpace x W k b) - (k+b)
    have hlo : k+b ≤ Module.finrank F (polynomialSpace x W k b) := by
      have h := Submodule.finrank_mono
        (show evalSpace x (k+b) ≤ polynomialSpace x W k b from le_sup_left)
      rw [finrank_evalSpace x hx (by omega : k+b ≤ n)] at h
      exact h
    have hhi := polynomialSpace_finrank_le_of_le_degree x hx W k s δ b hk hδ hN hd hsb
    have hdb : db ≤ δ := by dsimp [db]; omega
    have hdim : Module.finrank F (polynomialSpace x W k b) = k+b+db := by
      dsimp [db]; omega
    obtain ⟨E, hE, hgap⟩ := dimension_proximity_gap x hx W k b db hk
      (hdb.trans (hδ.trans hsb)) (by omega) hdim
    have hmatch (z : degreeLT F (k+b))
        (hz : k+b+δ ≤ (univ.filter fun j => batch x W B j = z.1.eval (x j)).card) :
        ∀ j, j ∉ E → batch x W B j = z.1.eval (x j) := by
      have h := (hgap 0 (zero_mem _) B z).2
        (by simpa only [zero_add] using (show k+b+db ≤
          (univ.filter fun j => batch x W B j = z.1.eval (x j)).card from by omega))
      simpa only [zero_add] using h
    have hcard : k+b ≤ (univ \ E).card := by
      have h := card_sdiff_add_card_eq_card (subset_univ E)
      simp only [card_univ, Fintype.card_fin] at h
      omega
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq (univ \ E) hx.injOn
    · exact (mem_degreeLT.mp p.2).trans_le (by exact_mod_cast hcard)
    · exact (mem_degreeLT.mp p'.2).trans_le (by exact_mod_cast hcard)
    · intro j hj
      exact (hmatch p hp j (mem_sdiff.mp hj).2).symm.trans
        (hmatch p' hp' j (mem_sdiff.mp hj).2)

end RecursivePolygero.ExtendedGap
