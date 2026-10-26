import LfzkV2.ConcreteFS
import Bcs.PotentialGrinding
import polygero.FiatShamir.Potential

/-! The actual V2 message prefixes followed by Polygero's challenge and
opening query. This is the schedule used by V1's graded potential compiler. -/

namespace LfzkV2.Replay

open SumcheckV2

variable {F Pad Slot C : Type} [Field F]

omit [Field F] in
private theorem decoded_vector_eq (decode : (n : ℕ) → C → Fin n → F)
    (first second : ℕ → C) (n start cut : ℕ)
    (hcut : start + vectorSlots n ≤ cut)
    (hanswers : ∀ j, j < cut → first j = second j) :
    decode n (first start) = decode n (second start) := by
  by_cases hn : n = 0
  · subst n
    funext i
    exact Fin.elim0 i
  · have hs : vectorSlots n = 1 := by simp [vectorSlots, hn]
    rw [hanswers start (by omega)]

omit [Field F] in
theorem readFrom_eq_of_prefix (decode : (n : ℕ) → C → Fin n → F)
    {out input : ℕ} (circuit : Circuit F out input)
    (plan : PadPlan (Pad := Pad) (Slot := Slot) circuit) (payload : Payload circuit)
    (first second : ℕ → C) (start : ℕ)
    (hanswers : ∀ j, j < start + layerSlots circuit → first j = second j) :
    readFrom decode circuit plan payload first start = readFrom decode circuit plan payload second start := by
  induction circuit generalizing start with
  | input => rfl
  | @layer out mid input a body rest ih =>
    have hb := decoded_vector_eq decode first second a start
      (start + layerSlots (.layer a body rest)) (by simp only [layerSlots]; omega) hanswers
    have hp : (fun i : Fin mid => decode 1 (first (start + vectorSlots a + i.val)) 0) =
        (fun i : Fin mid => decode 1 (second (start + vectorSlots a + i.val)) 0) := by
      funext i
      rw [hanswers _ (by simp only [layerSlots]; omega)]
    have ha := hanswers (start + vectorSlots a + mid) (by simp only [layerSlots]; omega)
    have hr := ih plan.2 payload.2 (start + vectorSlots a + mid + 1) (by
      intro j hj
      apply hanswers j
      simp only [layerSlots]
      omega)
    dsimp only [readFrom]
    rw [hb, hp, ha, hr]

@[ext] theorem _root_.LfzkV2.Reconstruction.ext {out input : ℕ} {circuit : Circuit F out input}
    {first second : Reconstruction circuit Pad Slot}
    (hmessages : first.messages = second.messages) (hpoint : first.point = second.point)
    (hconstraints : first.constraints = second.constraints) : first = second := by
  cases first
  cases second
  cases hmessages
  cases hpoint
  cases hconstraints
  rfl

theorem reconstructionFromAnswers_eq_of_prefix (decode : (n : ℕ) → C → Fin n → F)
    {out input : ℕ} (circuit : Circuit F out input)
    (plan : PadPlan (Pad := Pad) (Slot := Slot) circuit) (payload : Payload circuit)
    (first second : ℕ → C) (hanswers : ∀ j, j < slots circuit → first j = second j) :
    reconstructionFromAnswers decode circuit plan payload first =
      reconstructionFromAnswers decode circuit plan payload second := by
  have hm : read decode circuit plan payload first = read decode circuit plan payload second :=
    readFrom_eq_of_prefix decode circuit plan payload first second (vectorSlots out) hanswers
  have hp : outputPoint decode out first = outputPoint decode out second :=
    decoded_vector_eq decode first second out 0 (slots circuit) (by simp only [slots]; omega) hanswers
  apply Reconstruction.ext hm hp
  apply Option.some.inj
  rw [← (reconstructionFromAnswers decode circuit plan payload first).built,
    ← (reconstructionFromAnswers decode circuit plan payload second).built]
  exact congrArg buildConstraints (congrArg circuit.proof hm)

end LfzkV2.Replay

namespace LfzkV2.GradedReplay

open RecursivePolygero Bcs.TotalOracle ConcreteFS
open scoped Classical

variable {F C Key Parent : Type} [Field F] [Fintype F] [DecidableEq F]
variable {out input : ℕ}

variable (circuit : Circuit F out input) (I : Instance F)
variable (keyOf : Parent → Key) (payloadOf : Parent → Replay.Payload circuit)

def points : PrefixPoints (Domain Key circuit I Parent) where
  slot
    | .inl point => (Replay.points circuit).slot point
    | .inr (.inl _) => Replay.slots circuit
    | .inr (.inr _) => Replay.slots circuit + 1
  anc point j := match point with
    | .inl point => .inl ((Replay.points circuit).anc point j)
    | .inr (.inl parent) => .inl (Replay.hashInput circuit (keyOf parent) (payloadOf parent) j)
    | .inr (.inr (parent,_)) => if j < Replay.slots circuit then
        .inl (Replay.hashInput circuit (keyOf parent) (payloadOf parent) j)
      else ConcreteFS.parent circuit I parent
  anc_ne point j hj := by
    cases point with
    | inl point =>
      intro heq
      exact (Replay.points circuit).anc_ne point j hj (Sum.inl.inj heq)
    | inr point =>
      cases point with
      | inl parent => intro heq; cases heq
      | inr pair =>
        dsimp
        split_ifs <;> intro heq <;> cases heq

def hashInput (selected : Parent × I.layer.Payload) (j : ℕ) : Domain Key circuit I Parent :=
  if j < Replay.slots circuit then
    .inl (Replay.hashInput circuit (keyOf selected.1) (payloadOf selected.1) j)
  else if j = Replay.slots circuit then ConcreteFS.parent circuit I selected.1
  else ConcreteFS.child circuit I selected.1 selected.2

theorem hashInput_key (selected : Parent × I.layer.Payload) (j : ℕ) :
    Replay.queryKey circuit (ConcreteFS.roleKey I keyOf)
      (hashInput circuit I keyOf payloadOf selected j) = keyOf selected.1 := by
  unfold hashInput
  split_ifs
  · exact Replay.hashInput_key circuit _ _ _
  · rfl
  · rfl

theorem slot_hashInput (selected : Parent × I.layer.Payload)
    (j : ℕ) (hj : j < Replay.slots circuit + 2) :
    (points circuit I keyOf payloadOf).slot (hashInput circuit I keyOf payloadOf selected j) = j := by
  unfold hashInput
  split_ifs with hfield hchallenge
  · rw [Replay.hashInput_at circuit _ _ ⟨j,hfield⟩]
    rfl
  · exact hchallenge.symm
  · change Replay.slots circuit + 1 = j
    omega

theorem hashInput_injective (selected : Parent × I.layer.Payload) :
    Function.Injective (fun i : Fin (Replay.slots circuit + 2) =>
      hashInput circuit I keyOf payloadOf selected i.val) := by
  intro i j heq
  apply Fin.ext
  have h := congrArg (points circuit I keyOf payloadOf).slot heq
  simpa only [slot_hashInput circuit I keyOf payloadOf selected _ i.isLt,
    slot_hashInput circuit I keyOf payloadOf selected _ j.isLt] using h

theorem frontend_prefix (H : Domain Key circuit I Parent → C)
    (key : Key) (payload : Replay.Payload circuit) (i : Fin (Replay.slots circuit)) :
    (points circuit I keyOf payloadOf).chal H (.inl (Replay.pointAt circuit key payload i)) =
      fun j : Fin i.val => H (.inl (Replay.hashInput circuit key payload j.val)) :=
  Replay.queryPrefix_answers circuit H key payload i

theorem parent_prefix (H : Domain Key circuit I Parent → C) (parent : Parent) :
    (points circuit I keyOf payloadOf).chal H (ConcreteFS.parent circuit I parent) =
      fun j : Fin (Replay.slots circuit) =>
        H (.inl (Replay.hashInput circuit (keyOf parent) (payloadOf parent) j.val)) := rfl

theorem child_prefix (H : Domain Key circuit I Parent → C) (parent : Parent)
    (response : I.layer.Payload) (j : Fin (Replay.slots circuit + 1)) :
    (points circuit I keyOf payloadOf).chal H (ConcreteFS.child circuit I parent response) j =
      if j.val < Replay.slots circuit then
        H (.inl (Replay.hashInput circuit (keyOf parent) (payloadOf parent) j.val))
      else H (ConcreteFS.parent circuit I parent) := by
  dsimp only [PrefixPoints.chal, points, ConcreteFS.child]
  split_ifs <;> rfl

variable {Pad Slot : Type}

noncomputable def viewAt (decode : (n : ℕ) → C → Fin n → F) (dflt : C)
    (plan : Replay.PadPlan (Pad := Pad) (Slot := Slot) circuit)
    (parent : Parent) {m : ℕ} (pref : Fin m → C) : Reconstruction circuit Pad Slot :=
  Replay.reconstructionFromAnswers decode circuit plan (payloadOf parent) (Replay.fillAnswers dflt pref)

theorem parent_view_eq (decode : (n : ℕ) → C → Fin n → F) (dflt : C)
    (plan : Replay.PadPlan (Pad := Pad) (Slot := Slot) circuit)
    (H : Domain Key circuit I Parent → C) (parent : Parent) :
    viewAt circuit payloadOf decode dflt plan parent
        ((points circuit I keyOf payloadOf).chal H (ConcreteFS.parent circuit I parent)) =
      Replay.reconstruction decode circuit plan (keyOf parent) (payloadOf parent) H := by
  apply Replay.reconstructionFromAnswers_eq_of_prefix
  intro j hj
  rw [Replay.fillAnswers, dif_pos (show j < (points circuit I keyOf payloadOf).slot
    (ConcreteFS.parent circuit I parent) from hj)]
  rfl

theorem child_view_eq (decode : (n : ℕ) → C → Fin n → F) (dflt : C)
    (plan : Replay.PadPlan (Pad := Pad) (Slot := Slot) circuit)
    (H : Domain Key circuit I Parent → C) (parent : Parent) (response : I.layer.Payload) :
    viewAt circuit payloadOf decode dflt plan parent
        ((points circuit I keyOf payloadOf).chal H (ConcreteFS.child circuit I parent response)) =
      Replay.reconstruction decode circuit plan (keyOf parent) (payloadOf parent) H := by
  apply Replay.reconstructionFromAnswers_eq_of_prefix
  intro j hj
  rw [Replay.fillAnswers, dif_pos (show j < (points circuit I keyOf payloadOf).slot
    (ConcreteFS.child circuit I parent response) by change j < Replay.slots circuit + 1; omega)]
  exact (child_prefix circuit I keyOf payloadOf H parent response ⟨j,by omega⟩).trans (if_pos hj)

theorem child_coin_eq (H : Domain Key circuit I Parent → C) (parent : Parent)
    (response : I.layer.Payload) :
    (points circuit I keyOf payloadOf).chal H (ConcreteFS.child circuit I parent response)
        ⟨Replay.slots circuit,by change Replay.slots circuit < Replay.slots circuit + 1; omega⟩ =
      H (ConcreteFS.parent circuit I parent) := by
  rw [child_prefix, if_neg (Nat.lt_irrefl _)]

end LfzkV2.GradedReplay
