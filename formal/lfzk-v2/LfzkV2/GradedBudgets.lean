import LfzkV2.TwoFieldFS

/-! Closed forms of the exact slot sums used by the merged compiler. These
retain each side's field size and both terminal budgets separately. -/

namespace LfzkV2

open Finset RecursivePolygero

namespace GradedFS

variable {F C : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype C]
variable {out input bound cutoff : ℕ} (circuit : Circuit F out input) (I : Instance F)
variable (sampling : Replay.Sampling F C circuit)
variable {decodeCoin : C → I.layer.Coin} {decodeQuery : C → I.layer.Query}
variable (P : NonrecursiveFS.TerminalPotential I cutoff decodeCoin decodeQuery)

theorem slotBudget_sum :
    (∑ i : Fin (Replay.slots circuit+2), slotBudget (bound := bound) circuit I sampling P i) =
      sampling.unitFiber * bound * (out+circuit.sharpLayerBudget) + P.challengeBudget + P.queryBudget := by
  have hs : (∑ i : Fin (Replay.slots circuit),
      ((Replay.roleKind circuit ((Replay.roleEquiv circuit).symm i)).budget : ℚ)) =
        ((out+circuit.sharpLayerBudget : ℕ) : ℚ) := by
    exact_mod_cast Replay.budget_sum circuit
  have hfront : (∑ i : Fin (Replay.slots circuit),
      slotBudget (bound := bound) circuit I sampling P (i.castAdd 2)) =
      sampling.unitFiber * bound * (out+circuit.sharpLayerBudget) := by
    simp only [slotBudget, Fin.val_castAdd, dif_pos (Fin.isLt _)]
    rw [← Finset.mul_sum, ← Finset.mul_sum, hs]
    push_cast
    ring
  rw [Fin.sum_univ_add, hfront, Fin.sum_univ_two]
  simp [slotBudget]
  ring

end GradedFS

namespace TwoFieldFS

open TwoFieldReplay

variable {F₁ F₂ Key C Public Fmac : Type}
variable [Field F₁] [Fintype F₁] [DecidableEq F₁]
variable [Field F₂] [Fintype F₂] [DecidableEq F₂] [Fintype C]
variable [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {blocks : ℕ}
variable {out₁ input₁ out₂ input₂ : ℕ}
variable (circuit₁ : Circuit F₁ out₁ input₁) (I₁ : Instance F₁)
variable (circuit₂ : Circuit F₂ out₂ input₂) (I₂ : Instance F₂)
variable (S₁ : CompiledSide F₁ C (SideContext Key C Public) circuit₁ I₁)
variable (S₂ : CompiledSide F₂ C
  (SideContext Key C Public × FirstSnapshot Key C Public circuit₁ I₁) circuit₂ I₂)
variable (M : MacData C Fmac (Counting.tupleCounts I₁).Index (Counting.tupleCounts I₂).Index blocks)

theorem slotBudget_sum (proof : Proof Key C Public circuit₁ I₁ circuit₂ I₂) :
    (∑ i, slotBudget circuit₁ I₁ circuit₂ I₂ S₁ S₂ M i) =
      (S₁.bound*S₂.bound*M.fiber : ℕ) +
      (S₁.sampling.unitFiber * S₁.bound * (out₁+circuit₁.sharpLayerBudget) +
        S₁.potential.challengeBudget + S₁.potential.queryBudget) +
      (S₂.sampling.unitFiber * S₂.bound * (out₂+circuit₂.sharpLayerBudget) +
        S₂.potential.challengeBudget + S₂.potential.queryBudget) := by
  let b := TwoFieldPotential.budget circuit₁ I₁ circuit₂ I₂ S₁ S₂ M
  have hsum : (∑ i, slotBudget circuit₁ I₁ circuit₂ I₂ S₁ S₂ M i) =
      (S₁.bound*S₂.bound*M.fiber : ℕ) +
      (∑ i : Fin (Replay.slots circuit₁+2),
        GradedFS.slotBudget (bound := S₁.bound) circuit₁ I₁ S₁.sampling S₁.potential i) +
      (∑ i : Fin (Replay.slots circuit₂+2),
        GradedFS.slotBudget (bound := S₂.bound) circuit₂ I₂ S₂.sampling S₂.potential i) := by
    calc
      _ = ∑ i, b (hashInput circuit₁ I₁ circuit₂ I₂ proof i.val) :=
        sum_congr rfl (fun i _ => (budget_hashInput circuit₁ I₁ circuit₂ I₂ S₁ S₂ M proof i).symm)
      _ = b (.inl proof.context.1) +
          (∑ i : Fin (Replay.slots circuit₁+2),
            b (.inr (.inl (GradedReplay.hashInput circuit₁ I₁ Prod.fst Prod.snd
              (selectedOne circuit₁ I₁ circuit₂ I₂ proof) i.val)))) +
          (∑ i : Fin (Replay.slots circuit₂+2),
            b (.inr (.inr (GradedReplay.hashInput circuit₂ I₂ Prod.fst Prod.snd
              (selectedTwo circuit₁ I₁ circuit₂ I₂ proof) i.val)))) :=
        sum_hashInput circuit₁ I₁ circuit₂ I₂ proof b
      _ = _ := by
        change ((S₁.bound*S₂.bound*M.fiber : ℕ) : ℚ) + _ + _ = _
        congr 1
        · congr 1
          apply sum_congr rfl
          intro i _
          exact GradedFS.budget_hashInput (bound := S₁.bound) circuit₁ I₁ S₁.sampling
            Prod.fst Prod.snd S₁.potential (selectedOne circuit₁ I₁ circuit₂ I₂ proof) i
        · apply sum_congr rfl
          intro i _
          exact GradedFS.budget_hashInput (bound := S₂.bound) circuit₂ I₂ S₂.sampling
            Prod.fst Prod.snd S₂.potential (selectedTwo circuit₁ I₁ circuit₂ I₂ proof) i
  rw [hsum, GradedFS.slotBudget_sum, GradedFS.slotBudget_sum]

end TwoFieldFS
end LfzkV2
