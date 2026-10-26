import LfzkV2.GradedReplay

/-! V1's merged transcript blueprint: the key point, all first-side roles,
then all second-side roles. The second side carries the first side's complete
message history. Claimed key answers are public inputs carried by the proof. -/

namespace LfzkV2.TwoFieldReplay

open ConcreteFS RecursivePolygero Bcs.TotalOracle
open scoped Classical

variable {F₁ F₂ Key C Public : Type}
variable [Field F₁] [Fintype F₁] [DecidableEq F₁]
variable [Field F₂] [Fintype F₂] [DecidableEq F₂]
variable {out₁ input₁ out₂ input₂ : ℕ}

abbrev SideContext (Key C Public : Type) := Key × C × Public

abbrev ParentOne (Key C Public : Type) (circuit : Circuit F₁ out₁ input₁) :=
  SideContext Key C Public × Replay.Payload circuit

abbrev FirstSnapshot (Key C Public : Type) (circuit : Circuit F₁ out₁ input₁) (I : Instance F₁) :=
  ParentOne Key C Public circuit × I.layer.Payload

abbrev ParentTwo (Key C Public : Type) (circuit₁ : Circuit F₁ out₁ input₁) (I₁ : Instance F₁)
    (circuit₂ : Circuit F₂ out₂ input₂) :=
  (SideContext Key C Public × FirstSnapshot Key C Public circuit₁ I₁) × Replay.Payload circuit₂

structure Proof (Key C Public : Type) (circuit₁ : Circuit F₁ out₁ input₁) (I₁ : Instance F₁)
    (circuit₂ : Circuit F₂ out₂ input₂) (I₂ : Instance F₂) where
  context : SideContext Key C Public
  payloadOne : Replay.Payload circuit₁
  responseOne : I₁.layer.Payload
  payloadTwo : Replay.Payload circuit₂
  responseTwo : I₂.layer.Payload

variable (circuit₁ : Circuit F₁ out₁ input₁) (I₁ : Instance F₁)
variable (circuit₂ : Circuit F₂ out₂ input₂) (I₂ : Instance F₂)

def selectedOne (proof : Proof Key C Public circuit₁ I₁ circuit₂ I₂) :
    FirstSnapshot Key C Public circuit₁ I₁ := ((proof.context,proof.payloadOne),proof.responseOne)

def selectedTwo (proof : Proof Key C Public circuit₁ I₁ circuit₂ I₂) :
    ParentTwo Key C Public circuit₁ I₁ circuit₂ × I₂.layer.Payload :=
  (((proof.context,selectedOne circuit₁ I₁ circuit₂ I₂ proof),proof.payloadTwo),proof.responseTwo)

abbrev SideOne (Key C Public : Type) (circuit : Circuit F₁ out₁ input₁) (I : Instance F₁) :=
  ConcreteFS.Domain (SideContext Key C Public) circuit I (ParentOne Key C Public circuit)

abbrev SideTwo (Key C Public : Type) (circuit₁ : Circuit F₁ out₁ input₁) (I₁ : Instance F₁)
    (circuit₂ : Circuit F₂ out₂ input₂) (I₂ : Instance F₂) :=
  ConcreteFS.Domain (SideContext Key C Public × FirstSnapshot Key C Public circuit₁ I₁) circuit₂ I₂
    (ParentTwo Key C Public circuit₁ I₁ circuit₂)

abbrev Domain (Key C Public : Type) (circuit₁ : Circuit F₁ out₁ input₁) (I₁ : Instance F₁)
    (circuit₂ : Circuit F₂ out₂ input₂) (I₂ : Instance F₂) :=
  Key ⊕ (SideOne Key C Public circuit₁ I₁ ⊕ SideTwo Key C Public circuit₁ I₁ circuit₂ I₂)

def contextOne : SideOne Key C Public circuit₁ I₁ → SideContext Key C Public :=
  Replay.queryKey circuit₁ (roleKey I₁ Prod.fst)

def contextTwo : SideTwo Key C Public circuit₁ I₁ circuit₂ I₂ →
    SideContext Key C Public × FirstSnapshot Key C Public circuit₁ I₁ :=
  Replay.queryKey circuit₂ (roleKey I₂ Prod.fst)

def key : Domain Key C Public circuit₁ I₁ circuit₂ I₂ → Key
  | .inl k => k
  | .inr (.inl p) => (contextOne circuit₁ I₁ p).1
  | .inr (.inr p) => (contextTwo circuit₁ I₁ circuit₂ I₂ p).1.1

def pointsOne : PrefixPoints (SideOne Key C Public circuit₁ I₁) :=
  GradedReplay.points circuit₁ I₁ Prod.fst Prod.snd

def pointsTwo : PrefixPoints (SideTwo Key C Public circuit₁ I₁ circuit₂ I₂) :=
  GradedReplay.points circuit₂ I₂ Prod.fst Prod.snd

def points : PrefixPoints (Domain Key C Public circuit₁ I₁ circuit₂ I₂) where
  slot
    | .inl _ => 0
    | .inr (.inl p) => 1+(pointsOne circuit₁ I₁).slot p
    | .inr (.inr p) => 1+(Replay.slots circuit₁+2)+(pointsTwo circuit₁ I₁ circuit₂ I₂).slot p
  anc point j := match point with
    | .inl k => .inl k
    | .inr (.inl p) => if j = 0 then .inl (contextOne circuit₁ I₁ p).1 else
        .inr (.inl ((pointsOne circuit₁ I₁).anc p (j-1)))
    | .inr (.inr p) => if j = 0 then .inl (contextTwo circuit₁ I₁ circuit₂ I₂ p).1.1 else
        if j < 1+(Replay.slots circuit₁+2) then
          .inr (.inl (GradedReplay.hashInput circuit₁ I₁ Prod.fst Prod.snd
            (contextTwo circuit₁ I₁ circuit₂ I₂ p).2 (j-1)))
        else .inr (.inr ((pointsTwo circuit₁ I₁ circuit₂ I₂).anc p (j-1-(Replay.slots circuit₁+2))))
  anc_ne point j hj := by
    rcases point with k | p | p
    · change j < 0 at hj
      omega
    · dsimp
      split_ifs with hzero
      · intro heq; cases heq
      · intro heq
        exact (pointsOne circuit₁ I₁).anc_ne p (j-1)
          (by change j < 1+(pointsOne circuit₁ I₁).slot p at hj; omega)
          (Sum.inl.inj (Sum.inr.inj heq))
    · dsimp
      split_ifs with hzero hearlier
      · intro heq; cases heq
      · intro heq; cases heq
      · intro heq
        exact (pointsTwo circuit₁ I₁ circuit₂ I₂).anc_ne p (j-1-(Replay.slots circuit₁+2))
          (by change j < 1+(Replay.slots circuit₁+2)+(pointsTwo circuit₁ I₁ circuit₂ I₂).slot p at hj; omega)
          (Sum.inr.inj (Sum.inr.inj heq))

def hashInput (proof : Proof Key C Public circuit₁ I₁ circuit₂ I₂) (j : ℕ) :
    Domain Key C Public circuit₁ I₁ circuit₂ I₂ :=
  if j = 0 then .inl proof.context.1
  else if j < 1+(Replay.slots circuit₁+2) then
    .inr (.inl (GradedReplay.hashInput circuit₁ I₁ Prod.fst Prod.snd
      (selectedOne circuit₁ I₁ circuit₂ I₂ proof) (j-1)))
  else .inr (.inr (GradedReplay.hashInput circuit₂ I₂ Prod.fst Prod.snd
    (selectedTwo circuit₁ I₁ circuit₂ I₂ proof) (j-1-(Replay.slots circuit₁+2))))

theorem hashInput_zero (proof : Proof Key C Public circuit₁ I₁ circuit₂ I₂) :
    hashInput circuit₁ I₁ circuit₂ I₂ proof 0 = .inl proof.context.1 := by
  rw [hashInput, if_pos rfl]

theorem hashInput_one (proof : Proof Key C Public circuit₁ I₁ circuit₂ I₂)
    (i : Fin (Replay.slots circuit₁+2)) :
    hashInput circuit₁ I₁ circuit₂ I₂ proof (1+i.val) =
      .inr (.inl (GradedReplay.hashInput circuit₁ I₁ Prod.fst Prod.snd
        (selectedOne circuit₁ I₁ circuit₂ I₂ proof) i.val)) := by
  rw [hashInput, if_neg (by omega), if_pos (by omega), show 1+i.val-1=i.val by omega]

theorem hashInput_two (proof : Proof Key C Public circuit₁ I₁ circuit₂ I₂) (j : ℕ) :
    hashInput circuit₁ I₁ circuit₂ I₂ proof (1+(Replay.slots circuit₁+2)+j) =
      .inr (.inr (GradedReplay.hashInput circuit₂ I₂ Prod.fst Prod.snd
        (selectedTwo circuit₁ I₁ circuit₂ I₂ proof) j)) := by
  rw [hashInput, if_neg (by omega), if_neg (by omega),
    show 1+(Replay.slots circuit₁+2)+j-1-(Replay.slots circuit₁+2)=j by omega]

theorem hashInput_key (proof : Proof Key C Public circuit₁ I₁ circuit₂ I₂) (j : ℕ) :
    key circuit₁ I₁ circuit₂ I₂ (hashInput circuit₁ I₁ circuit₂ I₂ proof j) = proof.context.1 := by
  unfold hashInput
  split_ifs
  · rfl
  · exact congrArg Prod.fst (GradedReplay.hashInput_key circuit₁ I₁ Prod.fst Prod.snd
      (selectedOne circuit₁ I₁ circuit₂ I₂ proof) (j-1))
  · exact congrArg (fun ctx => ctx.1.1) (GradedReplay.hashInput_key circuit₂ I₂ Prod.fst Prod.snd
      (selectedTwo circuit₁ I₁ circuit₂ I₂ proof) (j-1-(Replay.slots circuit₁+2)))

theorem slot_hashInput (proof : Proof Key C Public circuit₁ I₁ circuit₂ I₂)
    (j : ℕ) (hj : j < 1+(Replay.slots circuit₁+2)+(Replay.slots circuit₂+2)) :
    (points circuit₁ I₁ circuit₂ I₂).slot (hashInput circuit₁ I₁ circuit₂ I₂ proof j) = j := by
  unfold hashInput
  split_ifs with hzero hone
  · exact hzero.symm
  · change 1+(GradedReplay.points circuit₁ I₁ Prod.fst Prod.snd).slot _ = j
    rw [GradedReplay.slot_hashInput circuit₁ I₁ Prod.fst Prod.snd _ _ (by omega)]
    omega
  · change 1+(Replay.slots circuit₁+2)+(GradedReplay.points circuit₂ I₂ Prod.fst Prod.snd).slot _ = j
    rw [GradedReplay.slot_hashInput circuit₂ I₂ Prod.fst Prod.snd _ _ (by omega)]
    omega

theorem hashInput_injective (proof : Proof Key C Public circuit₁ I₁ circuit₂ I₂) :
    Function.Injective (fun i : Fin (1+(Replay.slots circuit₁+2)+(Replay.slots circuit₂+2)) =>
      hashInput circuit₁ I₁ circuit₂ I₂ proof i.val) := by
  intro i j heq
  apply Fin.ext
  have h := congrArg (points circuit₁ I₁ circuit₂ I₂).slot heq
  simpa only [slot_hashInput circuit₁ I₁ circuit₂ I₂ proof _ i.isLt,
    slot_hashInput circuit₁ I₁ circuit₂ I₂ proof _ j.isLt] using h

theorem prefix_one (H : Domain Key C Public circuit₁ I₁ circuit₂ I₂ → C)
    (p : SideOne Key C Public circuit₁ I₁) (i : Fin ((pointsOne circuit₁ I₁).slot p)) :
    (points circuit₁ I₁ circuit₂ I₂).chal H (.inr (.inl p))
        ⟨1+i.val,by change 1+i.val < 1+(pointsOne circuit₁ I₁).slot p; omega⟩ =
      (pointsOne circuit₁ I₁).chal (fun x => H (.inr (.inl x))) p i := by
  dsimp only [PrefixPoints.chal, points]
  rw [if_neg (by omega), show 1+i.val-1=i.val by omega]

theorem prefix_one_key (H : Domain Key C Public circuit₁ I₁ circuit₂ I₂ → C)
    (p : SideOne Key C Public circuit₁ I₁) :
    (points circuit₁ I₁ circuit₂ I₂).chal H (.inr (.inl p))
        ⟨0,by change 0 < 1+(pointsOne circuit₁ I₁).slot p; omega⟩ =
      H (.inl (contextOne circuit₁ I₁ p).1) := rfl

theorem prefix_two (H : Domain Key C Public circuit₁ I₁ circuit₂ I₂ → C)
    (p : SideTwo Key C Public circuit₁ I₁ circuit₂ I₂)
    (i : Fin ((pointsTwo circuit₁ I₁ circuit₂ I₂).slot p)) :
    (points circuit₁ I₁ circuit₂ I₂).chal H (.inr (.inr p))
        ⟨1+(Replay.slots circuit₁+2)+i.val,by
          change 1+(Replay.slots circuit₁+2)+i.val <
            1+(Replay.slots circuit₁+2)+(pointsTwo circuit₁ I₁ circuit₂ I₂).slot p
          omega⟩ =
      (pointsTwo circuit₁ I₁ circuit₂ I₂).chal (fun x => H (.inr (.inr x))) p i := by
  dsimp only [PrefixPoints.chal, points]
  rw [if_neg (by omega), if_neg (by omega),
    show 1+(Replay.slots circuit₁+2)+i.val-1-(Replay.slots circuit₁+2)=i.val by omega]

theorem prefix_two_key (H : Domain Key C Public circuit₁ I₁ circuit₂ I₂ → C)
    (p : SideTwo Key C Public circuit₁ I₁ circuit₂ I₂) :
    (points circuit₁ I₁ circuit₂ I₂).chal H (.inr (.inr p))
        ⟨0,by change 0 < 1+(Replay.slots circuit₁+2)+(pointsTwo circuit₁ I₁ circuit₂ I₂).slot p; omega⟩ =
      H (.inl (contextTwo circuit₁ I₁ circuit₂ I₂ p).1.1) := rfl

theorem prefix_two_first (H : Domain Key C Public circuit₁ I₁ circuit₂ I₂ → C)
    (p : SideTwo Key C Public circuit₁ I₁ circuit₂ I₂) (i : Fin (Replay.slots circuit₁+2)) :
    (points circuit₁ I₁ circuit₂ I₂).chal H (.inr (.inr p))
        ⟨1+i.val,by
          change 1+i.val < 1+(Replay.slots circuit₁+2)+(pointsTwo circuit₁ I₁ circuit₂ I₂).slot p
          omega⟩ =
      H (.inr (.inl (GradedReplay.hashInput circuit₁ I₁ Prod.fst Prod.snd
        (contextTwo circuit₁ I₁ circuit₂ I₂ p).2 i.val))) := by
  dsimp only [PrefixPoints.chal, points]
  rw [if_neg (by omega), if_pos (by omega), show 1+i.val-1=i.val by omega]

/-- The exact sum over verifier roles, retaining both terminal charges of
each side rather than replacing them by one Boolean escape event. -/
theorem sum_hashInput {A : Type} [AddCommMonoid A]
    (proof : Proof Key C Public circuit₁ I₁ circuit₂ I₂)
    (f : Domain Key C Public circuit₁ I₁ circuit₂ I₂ → A) :
    (∑ i : Fin (1+(Replay.slots circuit₁+2)+(Replay.slots circuit₂+2)),
      f (hashInput circuit₁ I₁ circuit₂ I₂ proof i.val)) =
      f (.inl proof.context.1) +
      (∑ i : Fin (Replay.slots circuit₁+2), f (.inr (.inl
        (GradedReplay.hashInput circuit₁ I₁ Prod.fst Prod.snd (selectedOne circuit₁ I₁ circuit₂ I₂ proof) i.val)))) +
      (∑ i : Fin (Replay.slots circuit₂+2), f (.inr (.inr
        (GradedReplay.hashInput circuit₂ I₂ Prod.fst Prod.snd (selectedTwo circuit₁ I₁ circuit₂ I₂ proof) i.val)))) := by
  let g : ℕ → A := fun i => f (hashInput circuit₁ I₁ circuit₂ I₂ proof i)
  change (∑ i : Fin (1+(Replay.slots circuit₁+2)+(Replay.slots circuit₂+2)), g i.val) = _
  rw [Fin.sum_univ_eq_sum_range g, Finset.sum_range_add, Finset.sum_range_add, Finset.sum_range_one]
  have gzero : g 0 = f (.inl proof.context.1) := congrArg f (hashInput_zero circuit₁ I₁ circuit₂ I₂ proof)
  rw [gzero]
  congr 1
  · congr 1
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg f (hashInput_one circuit₁ I₁ circuit₂ I₂ proof i)
  · rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg f (hashInput_two circuit₁ I₁ circuit₂ I₂ proof i.val)

end LfzkV2.TwoFieldReplay
