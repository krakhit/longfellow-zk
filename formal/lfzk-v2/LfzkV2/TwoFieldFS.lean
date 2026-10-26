import LfzkV2.TwoFieldPotential
import Bcs.VerifierQuery

/-! V1's shared-query compiler for both V2 sides and their separate-witness
MAC. Every adversarial query pays the maximum local budget across all roles. -/

namespace LfzkV2.TwoFieldFS

open Finset RecursivePolygero Bcs.TotalOracle Merkle.RandomOracle TwoFieldReplay
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

noncomputable def maxBudget : ℚ :=
  max (S₁.bound*S₂.bound*M.fiber : ℕ)
    (max (GradedFS.maxBudget (bound := S₁.bound) circuit₁ I₁ S₁.sampling S₁.potential)
      (GradedFS.maxBudget (bound := S₂.bound) circuit₂ I₂ S₂.sampling S₂.potential))

theorem maxBudget_nonneg : 0 ≤ maxBudget circuit₁ I₁ circuit₂ I₂ S₁ S₂ M := by
  exact (Nat.cast_nonneg _).trans (le_max_left _ _)

theorem budget_le_max (point : Domain Key C Public circuit₁ I₁ circuit₂ I₂) :
    TwoFieldPotential.budget circuit₁ I₁ circuit₂ I₂ S₁ S₂ M point ≤
      maxBudget circuit₁ I₁ circuit₂ I₂ S₁ S₂ M := by
  unfold maxBudget TwoFieldPotential.budget
  rcases point with key | p | p
  · exact le_max_left _ _
  · exact (GradedFS.budget_le_max (bound := S₁.bound) circuit₁ I₁ S₁.sampling S₁.potential p).trans
      ((le_max_left _ _).trans (le_max_right _ _))
  · exact (GradedFS.budget_le_max (bound := S₂.bound) circuit₂ I₂ S₂.sampling S₂.potential p).trans
      ((le_max_right _ _).trans (le_max_right _ _))

noncomputable def slotBudget (i : Fin (1+(Replay.slots circuit₁+2)+(Replay.slots circuit₂+2))) : ℚ :=
  if hzero : i.val = 0 then (S₁.bound*S₂.bound*M.fiber : ℕ)
  else if hone : i.val < 1+(Replay.slots circuit₁+2) then
    GradedFS.slotBudget (bound := S₁.bound) circuit₁ I₁ S₁.sampling S₁.potential ⟨i.val-1,by omega⟩
  else GradedFS.slotBudget (bound := S₂.bound) circuit₂ I₂ S₂.sampling S₂.potential
    ⟨i.val-1-(Replay.slots circuit₁+2),by omega⟩

theorem budget_hashInput (proof : Proof Key C Public circuit₁ I₁ circuit₂ I₂)
    (i : Fin (1+(Replay.slots circuit₁+2)+(Replay.slots circuit₂+2))) :
    TwoFieldPotential.budget circuit₁ I₁ circuit₂ I₂ S₁ S₂ M
        (hashInput circuit₁ I₁ circuit₂ I₂ proof i.val) = slotBudget circuit₁ I₁ circuit₂ I₂ S₁ S₂ M i := by
  unfold hashInput slotBudget
  split_ifs with hzero hone
  · rfl
  · exact GradedFS.budget_hashInput (bound := S₁.bound) circuit₁ I₁ S₁.sampling Prod.fst Prod.snd S₁.potential
      (selectedOne circuit₁ I₁ circuit₂ I₂ proof) ⟨i.val-1,by omega⟩
  · exact GradedFS.budget_hashInput (bound := S₂.bound) circuit₂ I₂ S₂.sampling Prod.fst Prod.snd S₂.potential
      (selectedTwo circuit₁ I₁ circuit₂ I₂ proof) ⟨i.val-1-(Replay.slots circuit₁+2),by omega⟩

noncomputable def grinding
    [DecidableEq (Domain Key C Public circuit₁ I₁ circuit₂ I₂)]
    (tree : Tree (Domain Key C Public circuit₁ I₁ circuit₂ I₂) C Out N)
    (proofOf : Out → Proof Key C Public circuit₁ I₁ circuit₂ I₂)
    (context : (Domain Key C Public circuit₁ I₁ circuit₂ I₂ → C) → Key → I₁.layer.Oracle × I₂.layer.Oracle)
    (context_off : ∀ H H' x, AgreeOff x H H' →
      context H' (key circuit₁ I₁ circuit₂ I₂ x) = context H (key circuit₁ I₁ circuit₂ I₂ x)) :
    CtxGrinding C (Domain Key C Public circuit₁ I₁ circuit₂ I₂) Out Key
      (I₁.layer.Oracle × I₂.layer.Oracle) N (1+(Replay.slots circuit₁+2)+(Replay.slots circuit₂+2)) where
  adversary := tree
  hashInput out := hashInput circuit₁ I₁ circuit₂ I₂ (proofOf out)
  pts := points circuit₁ I₁ circuit₂ I₂
  key := key circuit₁ I₁ circuit₂ I₂
  ctxAt := context
  ctxAt_off := context_off
  Bad _ _ _ _ := False
  beta _ := 0
  bad_bound := by intros; simp

/-- The merged extraction/MAC bound for the actual two-field transcript.
The MAC rows are stated separately for each satisfying committed witness;
their private affine blinds may differ. -/
theorem extraction_le_of_total [Fintype Key] [Fintype Public]
    [Fintype (Replay.Payload circuit₁)] [Fintype (Replay.Payload circuit₂)]
    [DecidableEq (Domain Key C Public circuit₁ I₁ circuit₂ I₂)]
    (tree : Tree (Domain Key C Public circuit₁ I₁ circuit₂ I₂) C Out N)
    (proofOf : Out → Proof Key C Public circuit₁ I₁ circuit₂ I₂)
    (context : (Domain Key C Public circuit₁ I₁ circuit₂ I₂ → C) → Key → I₁.layer.Oracle × I₂.layer.Oracle)
    (context_off : ∀ H H' x, AgreeOff x H H' →
      context H' (key circuit₁ I₁ circuit₂ I₂ x) = context H (key circuit₁ I₁ circuit₂ I₂ x))
    (B : ℚ)
    (htotal : ∀ H, ∑ x ∈ (univ.filter fun x =>
        (grinding circuit₁ I₁ circuit₂ I₂ tree proofOf context context_off).Charged x H),
      TwoFieldPotential.budget circuit₁ I₁ circuit₂ I₂ S₁ S₂ M x ≤ B)
    (tag : Public → Fin blocks → Fmac)
    (hrowOne : ∀ (ctx : SideContext Key C Public) W g, S₁.Good ctx W g →
      M.macOne g (M.decode ctx.2.1) = tag ctx.2.2)
    (hrowTwo : ∀ (ctx : SideContext Key C Public × FirstSnapshot Key C Public circuit₁ I₁) W g,
      S₂.Good ctx W g → M.macTwo g (M.decode ctx.1.2.1) = tag ctx.1.2.2) :
    let fails := fun H : Domain Key C Public circuit₁ I₁ circuit₂ I₂ → C =>
      let proof := proofOf (tree.run H).1
      let W := context H proof.context.1
      proof.context.2.1 = H (.inl proof.context.1) ∧
      S₁.Accepts Prod.fst Prod.snd W.1 (fun x => H (.inr (.inl x))) (selectedOne circuit₁ I₁ circuit₂ I₂ proof) ∧
      S₂.Accepts Prod.fst Prod.snd W.2 (fun x => H (.inr (.inr x))) (selectedTwo circuit₁ I₁ circuit₂ I₂ proof) ∧
      TwoFieldPotential.extract circuit₁ I₁ circuit₂ I₂ S₁ S₂ M W proof = none
    ((univ.filter fails).card : ℚ)/(Fintype.card C : ℚ)^Fintype.card (Domain Key C Public circuit₁ I₁ circuit₂ I₂) ≤
      B/Fintype.card C := by
  letI : Nonempty C := ⟨S₁.dflt⟩
  intro fails
  let G := grinding circuit₁ I₁ circuit₂ I₂ tree proofOf context context_off
  refine G.potential_ratio_le_of_total
    (TwoFieldPotential.charge circuit₁ I₁ circuit₂ I₂ S₁ S₂ M)
    (TwoFieldPotential.charge_nonneg circuit₁ I₁ circuit₂ I₂ S₁ S₂ M)
    (TwoFieldPotential.budget circuit₁ I₁ circuit₂ I₂ S₁ S₂ M)
    (TwoFieldPotential.charge_sum_le circuit₁ I₁ circuit₂ I₂ S₁ S₂ M)
    B htotal fails ?_
  intro H hH
  let proof := proofOf (tree.run H).1
  let W := context H proof.context.1
  have hp := TwoFieldPotential.path_charge_ge_one circuit₁ I₁ circuit₂ I₂ S₁ S₂ M W H proof
    hH.1 hH.2.1 hH.2.2.1 (tag proof.context.2.2)
    (hrowOne proof.context W.1) (hrowTwo (proof.context,selectedOne circuit₁ I₁ circuit₂ I₂ proof) W.2)
    ((TwoFieldPotential.extract_none_iff circuit₁ I₁ circuit₂ I₂ S₁ S₂ M W proof).mp hH.2.2.2)
  let f := fun x : Domain Key C Public circuit₁ I₁ circuit₂ I₂ =>
    TwoFieldPotential.charge circuit₁ I₁ circuit₂ I₂ S₁ S₂ M (context H (G.key x)) x (G.pts.chal H x) (H x)
  apply le_trans _ (G.verifier_charge_le_total
    (fun out => hashInput_injective circuit₁ I₁ circuit₂ I₂ (proofOf out)) f
    (fun x => TwoFieldPotential.charge_nonneg circuit₁ I₁ circuit₂ I₂ S₁ S₂ M
      (context H (G.key x)) x (G.pts.chal H x) (H x)) H)
  refine hp.trans_eq ?_
  apply sum_congr rfl
  intro i _
  dsimp only [f]
  have hk : G.key (G.point H i.val) = proof.context.1 :=
    hashInput_key circuit₁ I₁ circuit₂ I₂ proof i.val
  rw [hk]
  rfl

/-- The usual shared adversarial-query budget and all verifier-slot costs. -/
theorem extraction_le [Fintype Key] [Fintype Public]
    [Fintype (Replay.Payload circuit₁)] [Fintype (Replay.Payload circuit₂)]
    [DecidableEq (Domain Key C Public circuit₁ I₁ circuit₂ I₂)]
    (tree : Tree (Domain Key C Public circuit₁ I₁ circuit₂ I₂) C Out N)
    (proofOf : Out → Proof Key C Public circuit₁ I₁ circuit₂ I₂)
    (context : (Domain Key C Public circuit₁ I₁ circuit₂ I₂ → C) → Key → I₁.layer.Oracle × I₂.layer.Oracle)
    (context_off : ∀ H H' x, AgreeOff x H H' →
      context H' (key circuit₁ I₁ circuit₂ I₂ x) = context H (key circuit₁ I₁ circuit₂ I₂ x))
    (tag : Public → Fin blocks → Fmac)
    (hrowOne : ∀ (ctx : SideContext Key C Public) W g, S₁.Good ctx W g →
      M.macOne g (M.decode ctx.2.1) = tag ctx.2.2)
    (hrowTwo : ∀ (ctx : SideContext Key C Public × FirstSnapshot Key C Public circuit₁ I₁) W g,
      S₂.Good ctx W g → M.macTwo g (M.decode ctx.1.2.1) = tag ctx.1.2.2) :
    let fails := fun H : Domain Key C Public circuit₁ I₁ circuit₂ I₂ → C =>
      let proof := proofOf (tree.run H).1
      let W := context H proof.context.1
      proof.context.2.1 = H (.inl proof.context.1) ∧
      S₁.Accepts Prod.fst Prod.snd W.1 (fun x => H (.inr (.inl x))) (selectedOne circuit₁ I₁ circuit₂ I₂ proof) ∧
      S₂.Accepts Prod.fst Prod.snd W.2 (fun x => H (.inr (.inr x))) (selectedTwo circuit₁ I₁ circuit₂ I₂ proof) ∧
      TwoFieldPotential.extract circuit₁ I₁ circuit₂ I₂ S₁ S₂ M W proof = none
    ((univ.filter fails).card : ℚ)/(Fintype.card C : ℚ)^Fintype.card (Domain Key C Public circuit₁ I₁ circuit₂ I₂) ≤
      (N*maxBudget circuit₁ I₁ circuit₂ I₂ S₁ S₂ M+
        ∑ i, slotBudget circuit₁ I₁ circuit₂ I₂ S₁ S₂ M i)/Fintype.card C := by
  let G := grinding circuit₁ I₁ circuit₂ I₂ tree proofOf context context_off
  exact extraction_le_of_total circuit₁ I₁ circuit₂ I₂ S₁ S₂ M tree proofOf context context_off _
    (G.charged_rational_budget_le
      (TwoFieldPotential.budget circuit₁ I₁ circuit₂ I₂ S₁ S₂ M)
      (TwoFieldPotential.budget_nonneg circuit₁ I₁ circuit₂ I₂ S₁ S₂ M)
      (maxBudget circuit₁ I₁ circuit₂ I₂ S₁ S₂ M) (maxBudget_nonneg circuit₁ I₁ circuit₂ I₂ S₁ S₂ M)
      (budget_le_max circuit₁ I₁ circuit₂ I₂ S₁ S₂ M) (slotBudget circuit₁ I₁ circuit₂ I₂ S₁ S₂ M)
      (fun out i => (budget_hashInput circuit₁ I₁ circuit₂ I₂ S₁ S₂ M (proofOf out) i).le))
    tag hrowOne hrowTwo

end LfzkV2.TwoFieldFS
