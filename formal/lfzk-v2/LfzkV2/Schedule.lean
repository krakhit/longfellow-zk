import LfzkV2.Replay
import LfzkV2.Transcript
import LfzkV2.Budgets

/-!
# The V2 hash-answer schedule

One nonempty output block, then one nonempty assertion block, the sumcheck
rounds, and the final-claim combination for each layer. The role equivalence
accounts for every answer exactly once, including scalar and empty layers.
-/

namespace LfzkV2.Replay

open SumcheckV2 ChallengeBlocks

variable {F : Type}

abbrev LayerRole : {out input : ℕ} → Circuit F out input → Type
  | _, _, .input => Fin 0
  | _, _, .layer (mid := mid) a _ rest =>
      Fin (vectorSlots a) ⊕ Fin mid ⊕ Fin 1 ⊕ LayerRole rest

private def fourSumEquiv (a b c d : ℕ) :
    (Fin a ⊕ Fin b ⊕ Fin c ⊕ Fin d) ≃ Fin (a+b+c+d) :=
  ((Equiv.refl (Fin a)).sumCongr ((Equiv.refl (Fin b)).sumCongr finSumFinEquiv)).trans
    (((Equiv.refl (Fin a)).sumCongr finSumFinEquiv).trans
      (finSumFinEquiv.trans (finCongr (by omega))))

def layerRoleEquiv : {out input : ℕ} → (circuit : Circuit F out input) →
    LayerRole circuit ≃ Fin (layerSlots circuit)
  | _, _, .input => Equiv.refl _
  | _, _, .layer (mid := mid) a _ rest =>
      ((Equiv.refl (Fin (vectorSlots a))).sumCongr
        ((Equiv.refl (Fin mid)).sumCongr
          ((Equiv.refl (Fin 1)).sumCongr (layerRoleEquiv rest)))).trans
        (fourSumEquiv (vectorSlots a) mid 1 (layerSlots rest))

def layerSlot {out input : ℕ} (circuit : Circuit F out input) (role : LayerRole circuit) : ℕ :=
  (layerRoleEquiv circuit role).val

theorem layerSlot_lt {out input : ℕ} (circuit : Circuit F out input) (role : LayerRole circuit) :
    layerSlot circuit role < layerSlots circuit := (layerRoleEquiv circuit role).isLt

theorem layerSlot_injective {out input : ℕ} (circuit : Circuit F out input) :
    Function.Injective (layerSlot circuit) := by
  intro a b h
  exact (layerRoleEquiv circuit).injective (Fin.ext h)

theorem layerSlot_assertions {out mid input a : ℕ}
    (body : CircuitLayer (Cube out) (Cube mid) (Fin a) F) (rest : Circuit F mid input)
    (i : Fin (vectorSlots a)) :
    layerSlot (.layer a body rest) (.inl i) = i.val := rfl

theorem layerSlot_round {out mid input a : ℕ}
    (body : CircuitLayer (Cube out) (Cube mid) (Fin a) F) (rest : Circuit F mid input) (i : Fin mid) :
    layerSlot (.layer a body rest) (.inr (.inl i)) = vectorSlots a + i.val := rfl

theorem layerSlot_combine {out mid input a : ℕ}
    (body : CircuitLayer (Cube out) (Cube mid) (Fin a) F) (rest : Circuit F mid input) (i : Fin 1) :
    layerSlot (.layer a body rest) (.inr (.inr (.inl i))) = vectorSlots a + mid := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  change vectorSlots a + (mid + 0) = _
  omega

theorem layerSlot_there {out mid input a : ℕ}
    (body : CircuitLayer (Cube out) (Cube mid) (Fin a) F) (rest : Circuit F mid input)
    (role : LayerRole rest) :
    layerSlot (.layer a body rest) (.inr (.inr (.inr role))) =
      vectorSlots a + mid + 1 + layerSlot rest role := by
  change vectorSlots a + (mid + (1 + layerSlot rest role)) = _
  omega

def LayerRole.kind : {out input : ℕ} → (circuit : Circuit F out input) → LayerRole circuit → Kind
  | _, _, .input, role => Fin.elim0 role
  | _, _, .layer a _ rest, role =>
      match role with
      | .inl _ => .assertions a
      | .inr (.inl _) => .round
      | .inr (.inr (.inl _)) => .combine
      | .inr (.inr (.inr role)) => LayerRole.kind rest role

theorem LayerRole.budget_le_two {out input : ℕ} (circuit : Circuit F out input) (role : LayerRole circuit) :
    (LayerRole.kind circuit role).budget ≤ 2 := by
  induction circuit with
  | input => exact Fin.elim0 role
  | layer a body rest ih =>
      rcases role with i | i | i | role
      · exact (Nat.min_le_left 1 a).trans (by omega)
      · exact le_refl 2
      · change 1 ≤ 2
        omega
      · exact ih role

abbrev Role {out input : ℕ} (circuit : Circuit F out input) :=
  Fin (vectorSlots out) ⊕ LayerRole circuit

def roleEquiv {out input : ℕ} (circuit : Circuit F out input) : Role circuit ≃ Fin (slots circuit) :=
  ((Equiv.refl (Fin (vectorSlots out))).sumCongr (layerRoleEquiv circuit)).trans finSumFinEquiv

def roleKind {out input : ℕ} (circuit : Circuit F out input) : Role circuit → Kind
  | .inl _ => .output out
  | .inr role => LayerRole.kind circuit role

theorem roleKind_budget_le {out input : ℕ} (circuit : Circuit F out input) (role : Role circuit) :
    (roleKind circuit role).budget ≤ max out 2 := by
  cases role with
  | inl _ => exact le_max_left _ _
  | inr role => exact (LayerRole.budget_le_two circuit role).trans (le_max_right _ _)

theorem layer_budget_sum {out input : ℕ} (circuit : Circuit F out input) :
    (∑ i : Fin (layerSlots circuit),
      (LayerRole.kind circuit ((layerRoleEquiv circuit).symm i)).budget) = circuit.sharpLayerBudget := by
  induction circuit with
  | input => simp [layerSlots, Circuit.sharpLayerBudget]
  | @layer out mid input a body rest ih =>
      let e := (Equiv.refl (Fin (vectorSlots a))).sumCongr
        ((Equiv.refl (Fin mid)).sumCongr ((Equiv.refl (Fin 1)).sumCongr (layerRoleEquiv rest)))
      let k := fun role => (LayerRole.kind (.layer a body rest) (e.symm role)).budget
      have hk role : (LayerRole.kind (.layer a body rest)
          ((layerRoleEquiv (.layer a body rest)).symm
            (fourSumEquiv (vectorSlots a) mid 1 (layerSlots rest) role))).budget = k role := by
        exact congrArg k ((fourSumEquiv (vectorSlots a) mid 1 (layerSlots rest)).symm_apply_apply role)
      refine ((fourSumEquiv (vectorSlots a) mid 1 (layerSlots rest)).sum_comp
        (fun i => (LayerRole.kind (.layer a body rest)
          ((layerRoleEquiv (.layer a body rest)).symm i)).budget)).symm.trans
            ((Finset.sum_congr rfl (fun role _ => hk role)).trans ?_)
      have ha : vectorSlots a * min 1 a = min 1 a := by
        cases a <;> simp [vectorSlots]
      simpa [k, e, Fintype.sum_sum_type,
        LayerRole.kind, ChallengeBlocks.Kind.budget, ih, ha, Circuit.sharpLayerBudget,
        Nat.mul_comm, Nat.add_assoc]

/-- The verifier's whole-block schedule has exactly the sharp algebraic
budget, with no charge for empty output or assertion draws. -/
theorem budget_sum {out input : ℕ} (circuit : Circuit F out input) :
    (∑ i : Fin (slots circuit),
      (roleKind circuit ((roleEquiv circuit).symm i)).budget) = out + circuit.sharpLayerBudget := by
  let e := (Equiv.refl (Fin (vectorSlots out))).sumCongr (layerRoleEquiv circuit)
  let k := fun role => (roleKind circuit (e.symm role)).budget
  have hk role : (roleKind circuit ((roleEquiv circuit).symm (finSumFinEquiv role))).budget = k role := by
    exact congrArg k (finSumFinEquiv.symm_apply_apply role)
  refine ((finSumFinEquiv : Fin (vectorSlots out) ⊕ Fin (layerSlots circuit) ≃
    Fin (slots circuit)).sum_comp
      (fun i => (roleKind circuit ((roleEquiv circuit).symm i)).budget)).symm.trans
        ((Finset.sum_congr rfl (fun role _ => hk role)).trans ?_)
  have hout : vectorSlots out * out = out := by
    cases out <;> simp [vectorSlots]
  simpa [k, e, Fintype.sum_sum_type, roleKind, ChallengeBlocks.Kind.budget, hout] using
    congrArg (fun n => out+n) (layer_budget_sum circuit)

inductive Message (F : Type) where
  | empty
  | round (polynomial : RoundPoly F)
  | claims (left right : F)
  deriving DecidableEq

def Message.equiv (F : Type) : Message F ≃ (Unit ⊕ (F × F) ⊕ (F × F)) where
  toFun
    | .empty => .inl ()
    | .round p => .inr (.inl (p.c0,p.c1))
    | .claims a b => .inr (.inr (a,b))
  invFun
    | .inl _ => .empty
    | .inr (.inl p) => .round ⟨p.1,p.2⟩
    | .inr (.inr p) => .claims p.1 p.2
  left_inv p := by cases p <;> rfl
  right_inv p := by rcases p with ⟨⟩ | p | p <;> rfl

instance [Fintype F] : Fintype (Message F) :=
  Fintype.ofEquiv (Unit ⊕ (F × F) ⊕ (F × F)) (Message.equiv F).symm

def layerMessage : {out input : ℕ} → (circuit : Circuit F out input) →
    Payload circuit → LayerRole circuit → Message F
  | _, _, .input, _, role => Fin.elim0 role
  | _, _, .layer _ _ rest, payload, role =>
      match role with
      | .inl _ => .empty
      | .inr (.inl i) => .round (payload.1.rounds i)
      | .inr (.inr (.inl _)) => .claims payload.1.claimA payload.1.claimB
      | .inr (.inr (.inr role)) => layerMessage rest payload.2 role

def message {out input : ℕ} (circuit : Circuit F out input) (payload : Payload circuit) : Role circuit → Message F
  | .inl _ => .empty
  | .inr role => layerMessage circuit payload role

def messageStream {out input : ℕ} (circuit : Circuit F out input) (payload : Payload circuit) : ℕ → Message F :=
  fun i => if h : i < slots circuit then message circuit payload ((roleEquiv circuit).symm ⟨i,h⟩) else .empty

theorem messageStream_at_role {out input : ℕ} (circuit : Circuit F out input) (payload : Payload circuit)
    (role : Role circuit) :
    messageStream circuit payload (roleEquiv circuit role).val = message circuit payload role := by
  simp [messageStream, (roleEquiv circuit role).isLt]

end LfzkV2.Replay
