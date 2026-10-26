import LfzkV2.GradedBudgets

/-! Field-normalized costs of the actual merged verifier. These equalities
connect numerical certificates to the raw-answer budgets used by the
adaptive oracle theorem. -/

namespace LfzkV2

open Finset RecursivePolygero

private theorem balanced_mul_div {fiber q c : ℕ} (h : fiber*q = c) (hc : 0 < c) (v : ℚ) :
    (fiber : ℚ)*v/c = v/q := by
  have hf : (fiber : ℚ) ≠ 0 := by
    have hn : fiber ≠ 0 := by intro hz; rw [hz, zero_mul] at h; omega
    exact_mod_cast hn
  rw [← h, Nat.cast_mul]
  exact mul_div_mul_left v (q : ℚ) hf

namespace GradedFS

variable {F C : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype C] [Nonempty C]
variable {out input bound cutoff : ℕ} (circuit : Circuit F out input) (I : Instance F)
variable (sampling : Replay.Sampling F C circuit)
variable {decodeCoin : C → I.layer.Coin} {decodeQuery : C → I.layer.Query}
variable (P : NonrecursiveFS.TerminalPotential I cutoff decodeCoin decodeQuery)

noncomputable def coefficient : ℚ :=
  max ((bound : ℚ)*max out 2/Fintype.card F)
    (max (P.challengeBudget/Fintype.card C) (P.queryBudget/Fintype.card C))

noncomputable def constant : ℚ :=
  (bound : ℚ)*(out+circuit.sharpLayerBudget)/Fintype.card F +
    P.challengeBudget/Fintype.card C + P.queryBudget/Fintype.card C

theorem maxBudget_div_eq :
    maxBudget (bound := bound) circuit I sampling P/Fintype.card C =
      coefficient (bound := bound) (out := out) I P := by
  unfold maxBudget coefficient
  rw [← max_div_div_right (Nat.cast_nonneg _), ← max_div_div_right (Nat.cast_nonneg _),
    balanced_mul_div sampling.balanced Fintype.card_pos]

theorem slotBudget_sum_div_eq :
    (∑ i, slotBudget (bound := bound) circuit I sampling P i)/Fintype.card C =
      constant (bound := bound) circuit I P := by
  rw [slotBudget_sum, add_div, add_div]
  unfold constant
  congr 2
  rw [mul_assoc, balanced_mul_div sampling.balanced Fintype.card_pos]

end GradedFS

namespace TwoFieldFS

open TwoFieldReplay

variable {F₁ F₂ Key C Public Fmac : Type}
variable [Field F₁] [Fintype F₁] [DecidableEq F₁]
variable [Field F₂] [Fintype F₂] [DecidableEq F₂] [Fintype C] [Nonempty C]
variable [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {blocks : ℕ}
variable {out₁ input₁ out₂ input₂ : ℕ}
variable (circuit₁ : Circuit F₁ out₁ input₁) (I₁ : Instance F₁)
variable (circuit₂ : Circuit F₂ out₂ input₂) (I₂ : Instance F₂)
variable (S₁ : CompiledSide F₁ C (SideContext Key C Public) circuit₁ I₁)
variable (S₂ : CompiledSide F₂ C
  (SideContext Key C Public × FirstSnapshot Key C Public circuit₁ I₁) circuit₂ I₂)
variable (M : MacData C Fmac (Counting.tupleCounts I₁).Index (Counting.tupleCounts I₂).Index blocks)

noncomputable def macCost : ℚ := (S₁.bound : ℚ)*S₂.bound/Fintype.card Fmac

noncomputable def coefficient : ℚ :=
  max (macCost (Fmac := Fmac) circuit₁ I₁ circuit₂ I₂ S₁ S₂)
    (max (GradedFS.coefficient (bound := S₁.bound) (out := out₁) I₁ S₁.potential)
      (GradedFS.coefficient (bound := S₂.bound) (out := out₂) I₂ S₂.potential))

noncomputable def constant : ℚ :=
  macCost (Fmac := Fmac) circuit₁ I₁ circuit₂ I₂ S₁ S₂ + GradedFS.constant (bound := S₁.bound) circuit₁ I₁ S₁.potential +
    GradedFS.constant (bound := S₂.bound) circuit₂ I₂ S₂.potential

theorem macBudget_div_eq :
    ((S₁.bound*S₂.bound*M.fiber : ℕ) : ℚ)/Fintype.card C =
      macCost (Fmac := Fmac) circuit₁ I₁ circuit₂ I₂ S₁ S₂ := by
  unfold macCost
  push_cast
  rw [show (S₁.bound : ℚ)*S₂.bound*M.fiber = (M.fiber : ℚ)*((S₁.bound : ℚ)*S₂.bound) by ring]
  exact balanced_mul_div M.balanced Fintype.card_pos _

theorem maxBudget_div_eq :
    maxBudget circuit₁ I₁ circuit₂ I₂ S₁ S₂ M/Fintype.card C =
      coefficient (Fmac := Fmac) circuit₁ I₁ circuit₂ I₂ S₁ S₂ := by
  unfold maxBudget coefficient
  rw [← max_div_div_right (Nat.cast_nonneg _), ← max_div_div_right (Nat.cast_nonneg _),
    macBudget_div_eq circuit₁ I₁ circuit₂ I₂ S₁ S₂ M,
    GradedFS.maxBudget_div_eq, GradedFS.maxBudget_div_eq]

theorem slotBudget_sum_div_eq (proof : Proof Key C Public circuit₁ I₁ circuit₂ I₂) :
    (∑ i, slotBudget circuit₁ I₁ circuit₂ I₂ S₁ S₂ M i)/Fintype.card C =
      constant (Fmac := Fmac) circuit₁ I₁ circuit₂ I₂ S₁ S₂ := by
  rw [slotBudget_sum circuit₁ I₁ circuit₂ I₂ S₁ S₂ M proof, add_div, add_div]
  unfold constant
  rw [macBudget_div_eq circuit₁ I₁ circuit₂ I₂ S₁ S₂ M]
  congr 1
  · congr 1
    rw [← GradedFS.slotBudget_sum, GradedFS.slotBudget_sum_div_eq]
  · rw [← GradedFS.slotBudget_sum, GradedFS.slotBudget_sum_div_eq]

/-- The coefficient and constant below are exactly those in the checked
authenticated extraction theorem, before adding its Merkle error. -/
theorem error_eq (N : ℕ) (proof : Proof Key C Public circuit₁ I₁ circuit₂ I₂) :
    (N*maxBudget circuit₁ I₁ circuit₂ I₂ S₁ S₂ M +
      ∑ i, slotBudget circuit₁ I₁ circuit₂ I₂ S₁ S₂ M i)/Fintype.card C =
      N*coefficient (Fmac := Fmac) circuit₁ I₁ circuit₂ I₂ S₁ S₂ +
        constant (Fmac := Fmac) circuit₁ I₁ circuit₂ I₂ S₁ S₂ := by
  rw [add_div, mul_div_assoc, maxBudget_div_eq,
    slotBudget_sum_div_eq circuit₁ I₁ circuit₂ I₂ S₁ S₂ M proof]

end TwoFieldFS
end LfzkV2
