import LfzkV2.TwoFieldFS
import LfzkV2.TwoFieldKeyReplay

/-! The merged bound for raw proofs whose MAC answer is recomputed by the
verifier. The annotation lookup is already a verifier slot, so the query
coefficient still counts only the original prover's N queries. -/

namespace LfzkV2.TwoFieldFS

open Finset RecursivePolygero Merkle.RandomOracle Bcs.TotalOracle TwoFieldReplay
open scoped Classical

variable {F₁ F₂ Key C Public Fmac Out : Type}
variable [Field F₁] [Fintype F₁] [DecidableEq F₁]
variable [Field F₂] [Fintype F₂] [DecidableEq F₂] [Fintype C]
variable [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {blocks N : ℕ}
variable {out₁ input₁ out₂ input₂ : ℕ}
variable (circuit₁ : Circuit F₁ out₁ input₁) (I₁ : Instance F₁)
variable (circuit₂ : Circuit F₂ out₂ input₂) (I₂ : Instance F₂)
variable (S₁ : CompiledSide F₁ C (SideContext Key C Public) circuit₁ I₁)
variable (S₂ : CompiledSide F₂ C
  (SideContext Key C Public × FirstSnapshot Key C Public circuit₁ I₁) circuit₂ I₂)
variable (M : MacData C Fmac (Counting.tupleCounts I₁).Index (Counting.tupleCounts I₂).Index blocks)

theorem prepared_extraction_le [Fintype Key] [Fintype Public]
    [Fintype (Replay.Payload circuit₁)] [Fintype (Replay.Payload circuit₂)]
    [DecidableEq (Domain Key C Public circuit₁ I₁ circuit₂ I₂)]
    (tree : Tree (Domain Key C Public circuit₁ I₁ circuit₂ I₂) C Out N)
    (proofOf : Out → RawProof (Key := Key) (Public := Public) circuit₁ I₁ circuit₂ I₂)
    (context : (Domain Key C Public circuit₁ I₁ circuit₂ I₂ → C) → Key → I₁.layer.Oracle × I₂.layer.Oracle)
    (context_off : ∀ H H' x, AgreeOff x H H' →
      context H' (key circuit₁ I₁ circuit₂ I₂ x) = context H (key circuit₁ I₁ circuit₂ I₂ x))
    (tag : Public → Fin blocks → Fmac)
    (hrowOne : ∀ (ctx : SideContext Key C Public) W g, S₁.Good ctx W g →
      M.macOne g (M.decode ctx.2.1) = tag ctx.2.2)
    (hrowTwo : ∀ (ctx : SideContext Key C Public × FirstSnapshot Key C Public circuit₁ I₁) W g,
      S₂.Good ctx W g → M.macTwo g (M.decode ctx.1.2.1) = tag ctx.1.2.2) :
    let fails := fun H : Domain Key C Public circuit₁ I₁ circuit₂ I₂ → C =>
      let raw := proofOf (tree.run H).1
      let proof := annotate circuit₁ I₁ circuit₂ I₂ raw (H (.inl (rawKey circuit₁ I₁ circuit₂ I₂ raw)))
      let W := context H proof.context.1
      S₁.Accepts Prod.fst Prod.snd W.1 (fun x => H (.inr (.inl x))) (selectedOne circuit₁ I₁ circuit₂ I₂ proof) ∧
      S₂.Accepts Prod.fst Prod.snd W.2 (fun x => H (.inr (.inr x))) (selectedTwo circuit₁ I₁ circuit₂ I₂ proof) ∧
      TwoFieldPotential.extract circuit₁ I₁ circuit₂ I₂ S₁ S₂ M W proof = none
    ((univ.filter fails).card : ℚ)/(Fintype.card C : ℚ)^Fintype.card (Domain Key C Public circuit₁ I₁ circuit₂ I₂) ≤
      (N*maxBudget circuit₁ I₁ circuit₂ I₂ S₁ S₂ M+
        ∑ i, slotBudget circuit₁ I₁ circuit₂ I₂ S₁ S₂ M i)/Fintype.card C := by
  letI : Nonempty C := ⟨S₁.dflt⟩
  intro fails
  let point : Out → Domain Key C Public circuit₁ I₁ circuit₂ I₂ :=
    fun out => Sum.inl (rawKey circuit₁ I₁ circuit₂ I₂ (proofOf out))
  let prepared := VerifierQuery.prepare tree point
  let output := preparedProof (C := C) circuit₁ I₁ circuit₂ I₂ proofOf
  let G := grinding circuit₁ I₁ circuit₂ I₂ prepared output context context_off
  have htotal := G.verifierQuery_budget_le tree point rfl (by omega)
    (fun out c => preparedProof_key_input circuit₁ I₁ circuit₂ I₂ proofOf out c)
    (TwoFieldPotential.budget circuit₁ I₁ circuit₂ I₂ S₁ S₂ M)
    (TwoFieldPotential.budget_nonneg circuit₁ I₁ circuit₂ I₂ S₁ S₂ M)
    (maxBudget circuit₁ I₁ circuit₂ I₂ S₁ S₂ M) (maxBudget_nonneg circuit₁ I₁ circuit₂ I₂ S₁ S₂ M)
    (budget_le_max circuit₁ I₁ circuit₂ I₂ S₁ S₂ M) (slotBudget circuit₁ I₁ circuit₂ I₂ S₁ S₂ M)
    (fun out i => (budget_hashInput circuit₁ I₁ circuit₂ I₂ S₁ S₂ M (output out) i).le)
  have h := extraction_le_of_total circuit₁ I₁ circuit₂ I₂ S₁ S₂ M prepared output context context_off
    _ htotal tag hrowOne hrowTwo
  apply le_trans _ h
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply (Nat.cast_le (α := ℚ)).mpr
  apply card_le_card
  intro H hH
  simp only [mem_filter] at hH ⊢
  refine ⟨hH.1,preparedProof_coherent circuit₁ I₁ circuit₂ I₂ tree proofOf H,?_,?_,?_⟩
  · simpa only [prepared,point,output,VerifierQuery.prepare_output,preparedProof] using hH.2.1
  · simpa only [prepared,point,output,VerifierQuery.prepare_output,preparedProof] using hH.2.2.1
  · simpa only [prepared,point,output,VerifierQuery.prepare_output,preparedProof] using hH.2.2.2

end LfzkV2.TwoFieldFS
