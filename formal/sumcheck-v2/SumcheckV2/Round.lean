import SumcheckV2.RoundPoly

/-!
# One v2 round

There is no separate affine endpoint check. The reconstructed polynomial has
projective sum equal to the incoming claim by construction. A false incoming
claim can become true only at a root of a nonzero quadratic difference.
-/

namespace SumcheckV2

open Classical Polynomial

variable {F : Type} [Field F]

def check_round (claim : F) (message : RoundPoly F) (z : F) : F :=
  message.eval claim z

def BadRoundEvent (P : Polynomial F) (message : RoundPoly F) (claim z : F) : Prop :=
  claim ≠ projectiveSum P ∧ check_round claim message z = P.eval z

theorem sumcheck_step_reduction (P : Polynomial F) (message : RoundPoly F) (claim z : F)
    (hfalse : claim ≠ projectiveSum P) :
    check_round claim message z ≠ P.eval z ∨ BadRoundEvent P message claim z := by
  by_cases h : check_round claim message z = P.eval z
  · exact Or.inr ⟨hfalse, h⟩
  · exact Or.inl h

theorem sumcheck_step_completeness (P : Polynomial F) (hdeg : P.natDegree ≤ 2) (z : F) :
    check_round (projectiveSum P) (RoundPoly.ofPoly P) z = P.eval z :=
  RoundPoly.eval_ofPoly P hdeg z

/-- At most two challenges can repair a false incoming claim. -/
theorem bad_round_roots [Fintype F] [DecidableEq F]
    (P : Polynomial F) (message : RoundPoly F) (claim : F) (hdeg : P.natDegree ≤ 2) :
    (Finset.univ.filter fun z => BadRoundEvent P message claim z).card ≤ 2 := by
  by_cases hfalse : claim ≠ projectiveSum P
  · have hnonzero := message.toPoly_sub_ne_zero P claim hfalse
    have hsubset : (Finset.univ.filter fun z => BadRoundEvent P message claim z) ⊆
        (message.toPoly claim - P).roots.toFinset := by
      intro z hz
      have heq := (Finset.mem_filter.mp hz).2.2
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hnonzero]
      simpa [Polynomial.IsRoot, check_round] using sub_eq_zero.mpr heq
    calc
      _ ≤ (message.toPoly claim - P).roots.toFinset.card := Finset.card_le_card hsubset
      _ ≤ (message.toPoly claim - P).roots.card := Multiset.toFinset_card_le _
      _ ≤ (message.toPoly claim - P).natDegree := Polynomial.card_roots' _
      _ ≤ max (message.toPoly claim).natDegree P.natDegree := Polynomial.natDegree_sub_le _ _
      _ ≤ 2 := max_le (message.toPoly_natDegree claim) hdeg
  · simp [BadRoundEvent, hfalse]

end SumcheckV2
