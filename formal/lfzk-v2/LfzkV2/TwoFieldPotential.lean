import LfzkV2.CompiledSide
import LfzkV2.TwoFieldReplay
import LfzkV2.Mac
import LfzkV1.MacSep

/-! V1's merged graded charge: a separate-witness MAC collision at the key
point, and each actual V2 side's field/challenge/query potential afterwards. -/

namespace LfzkV2

open Finset RecursivePolygero Bcs.TotalOracle
open scoped Classical

structure MacData (C Fmac WitnessOne WitnessTwo : Type) [Fintype C]
    [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] (blocks : ℕ) where
  commonOne : WitnessOne → Fin blocks → Fmac
  commonTwo : WitnessTwo → Fin blocks → Fmac
  blindOne : WitnessOne → Fin blocks → Fmac
  blindTwo : WitnessTwo → Fin blocks → Fmac
  decode : C → Fmac
  fiber : ℕ
  fiber_bound : ∀ x, (univ.filter fun c : C => decode c = x).card ≤ fiber
  balanced : fiber * Fintype.card Fmac = Fintype.card C

namespace MacData

variable {C Fmac WitnessOne WitnessTwo : Type}
variable [Fintype C] [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {blocks : ℕ}

/-- V2 shares the verifier multiplier across blocks and adds each private pad. -/
def macOne (M : MacData C Fmac WitnessOne WitnessTwo blocks) (a : WitnessOne) (x : Fmac) : Fin blocks → Fmac :=
  Mac.tag x (M.blindOne a) (M.commonOne a)

def macTwo (M : MacData C Fmac WitnessOne WitnessTwo blocks) (b : WitnessTwo) (x : Fmac) : Fin blocks → Fmac :=
  Mac.tag x (M.blindTwo b) (M.commonTwo b)

theorem collision (M : MacData C Fmac WitnessOne WitnessTwo blocks) (a : WitnessOne) (b : WitnessTwo)
    (hne : M.commonOne a ≠ M.commonTwo b) :
    (univ.filter fun x => M.macOne a x = M.macTwo b x).card ≤ 1 :=
  Mac.collision_card_le_one (M.blindOne a) (M.blindTwo b) _ _ hne

/-- V2's affine MAC data; the two sides supply separate private pads. -/
def affine (commonOne : WitnessOne → Fin blocks → Fmac) (commonTwo : WitnessTwo → Fin blocks → Fmac)
    (blindOne : WitnessOne → Fin blocks → Fmac) (blindTwo : WitnessTwo → Fin blocks → Fmac)
    (decode : C → Fmac) (fiber : ℕ)
    (hbalance : ∀ x, (univ.filter fun c : C => decode c = x).card ≤ fiber)
    (hcard : fiber * Fintype.card Fmac = Fintype.card C) :
    MacData C Fmac WitnessOne WitnessTwo blocks where
  commonOne := commonOne
  commonTwo := commonTwo
  blindOne := blindOne
  blindTwo := blindTwo
  decode := decode
  fiber := fiber
  fiber_bound := hbalance
  balanced := hcard

variable (M : MacData C Fmac WitnessOne WitnessTwo blocks)

def Bad (one : Finset WitnessOne) (two : Finset WitnessTwo) (c : C) : Prop :=
  LfzkV1.MacSep.SepMacBad one two M.commonOne M.commonTwo M.macOne M.macTwo (M.decode c)

theorem charge_sum_le (one : Finset WitnessOne) (two : Finset WitnessTwo)
    (B₁ B₂ : ℕ) (h₁ : one.card ≤ B₁) (h₂ : two.card ≤ B₂) :
    (∑ c : C, RecursivePolygero.indicator (M.Bad one two c)) ≤ (B₁*B₂*M.fiber : ℕ) := by
  have h := (LfzkV1.MacSep.sepMacBad_card_le one two M.commonOne M.commonTwo M.macOne M.macTwo
    M.collision 0 M.decode M.fiber_bound).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul h₁ h₂))
  have hc : (univ.filter (M.Bad one two)).card ≤ B₁*B₂*M.fiber := by
    apply le_trans (card_le_card ?_) h
    intro c hc
    simp only [mem_filter] at hc ⊢
    simpa only [Bad, zero_add] using hc
  have hq := (Nat.cast_le (α := ℚ)).mpr hc
  simpa only [RecursivePolygero.indicator, sum_boole] using hq

end MacData

namespace TwoFieldPotential

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

def sliceOne (p : SideOne Key C Public circuit₁ I₁)
    (pref : Fin ((points circuit₁ I₁ circuit₂ I₂).slot (.inr (.inl p))) → C) :
    Fin ((pointsOne circuit₁ I₁).slot p) → C :=
  fun i => pref ⟨1+i.val,by change 1+i.val < 1+(pointsOne circuit₁ I₁).slot p; omega⟩

def sliceTwo (p : SideTwo Key C Public circuit₁ I₁ circuit₂ I₂)
    (pref : Fin ((points circuit₁ I₁ circuit₂ I₂).slot (.inr (.inr p))) → C) :
    Fin ((pointsTwo circuit₁ I₁ circuit₂ I₂).slot p) → C :=
  fun i => pref ⟨1+(Replay.slots circuit₁+2)+i.val,by
    change 1+(Replay.slots circuit₁+2)+i.val <
      1+(Replay.slots circuit₁+2)+(pointsTwo circuit₁ I₁ circuit₂ I₂).slot p
    omega⟩

noncomputable def charge (W : I₁.layer.Oracle × I₂.layer.Oracle)
    (point : Domain Key C Public circuit₁ I₁ circuit₂ I₂)
    (pref : Fin ((points circuit₁ I₁ circuit₂ I₂).slot point) → C) (c : C) : ℚ :=
  match point with
  | .inl _ => RecursivePolygero.indicator
    (M.Bad (Counting.committedCandidates I₁ W.1 S₁.cutoff) (Counting.committedCandidates I₂ W.2 S₂.cutoff) c)
  | .inr (.inl p) => S₁.charge Prod.fst Prod.snd W.1 p (sliceOne circuit₁ I₁ circuit₂ I₂ p pref) c
  | .inr (.inr p) => S₂.charge Prod.fst Prod.snd W.2 p (sliceTwo circuit₁ I₁ circuit₂ I₂ p pref) c

noncomputable def budget (point : Domain Key C Public circuit₁ I₁ circuit₂ I₂) : ℚ :=
  match point with
  | .inl _ => (S₁.bound*S₂.bound*M.fiber : ℕ)
  | .inr (.inl p) => GradedFS.budget (bound := S₁.bound) circuit₁ I₁ S₁.sampling S₁.potential p
  | .inr (.inr p) => GradedFS.budget (bound := S₂.bound) circuit₂ I₂ S₂.sampling S₂.potential p

theorem charge_nonneg (W : I₁.layer.Oracle × I₂.layer.Oracle)
    (point : Domain Key C Public circuit₁ I₁ circuit₂ I₂)
    (pref : Fin ((points circuit₁ I₁ circuit₂ I₂).slot point) → C) (c : C) :
    0 ≤ charge circuit₁ I₁ circuit₂ I₂ S₁ S₂ M W point pref c := by
  rcases point with key | p | p
  · exact RecursivePolygero.indicator_nonneg _
  · exact S₁.charge_nonneg Prod.fst Prod.snd W.1 p _ c
  · exact S₂.charge_nonneg Prod.fst Prod.snd W.2 p _ c

theorem budget_nonneg (point : Domain Key C Public circuit₁ I₁ circuit₂ I₂) :
    0 ≤ budget circuit₁ I₁ circuit₂ I₂ S₁ S₂ M point := by
  rcases point with key | p | p
  · exact Nat.cast_nonneg _
  · exact GradedFS.budget_nonneg (bound := S₁.bound) circuit₁ I₁ S₁.sampling S₁.potential p
  · exact GradedFS.budget_nonneg (bound := S₂.bound) circuit₂ I₂ S₂.sampling S₂.potential p

theorem charge_sum_le (W : I₁.layer.Oracle × I₂.layer.Oracle)
    (point : Domain Key C Public circuit₁ I₁ circuit₂ I₂)
    (pref : Fin ((points circuit₁ I₁ circuit₂ I₂).slot point) → C) :
    (∑ c : C, charge circuit₁ I₁ circuit₂ I₂ S₁ S₂ M W point pref c) ≤
      budget circuit₁ I₁ circuit₂ I₂ S₁ S₂ M point := by
  rcases point with key | p | p
  · exact M.charge_sum_le _ _ S₁.bound S₂.bound
      (Counting.committedCandidates_card_le I₁ W.1 S₁.cutoff S₁.bound S₁.cutoff_gt S₁.packing)
      (Counting.committedCandidates_card_le I₂ W.2 S₂.cutoff S₂.bound S₂.cutoff_gt S₂.packing)
  · exact S₁.charge_sum_le Prod.fst Prod.snd W.1 p _
  · exact S₂.charge_sum_le Prod.fst Prod.snd W.2 p _

theorem charge_one_eq (W : I₁.layer.Oracle × I₂.layer.Oracle)
    (H : Domain Key C Public circuit₁ I₁ circuit₂ I₂ → C) (p : SideOne Key C Public circuit₁ I₁) :
    charge circuit₁ I₁ circuit₂ I₂ S₁ S₂ M W (.inr (.inl p))
        ((points circuit₁ I₁ circuit₂ I₂).chal H (.inr (.inl p))) (H (.inr (.inl p))) =
      S₁.charge Prod.fst Prod.snd W.1 p ((pointsOne circuit₁ I₁).chal (fun x => H (.inr (.inl x))) p)
        (H (.inr (.inl p))) := by
  change S₁.charge Prod.fst Prod.snd W.1 p _ _ = _
  congr 1
  funext i
  exact prefix_one circuit₁ I₁ circuit₂ I₂ H p i

theorem charge_two_eq (W : I₁.layer.Oracle × I₂.layer.Oracle)
    (H : Domain Key C Public circuit₁ I₁ circuit₂ I₂ → C)
    (p : SideTwo Key C Public circuit₁ I₁ circuit₂ I₂) :
    charge circuit₁ I₁ circuit₂ I₂ S₁ S₂ M W (.inr (.inr p))
        ((points circuit₁ I₁ circuit₂ I₂).chal H (.inr (.inr p))) (H (.inr (.inr p))) =
      S₂.charge Prod.fst Prod.snd W.2 p ((pointsTwo circuit₁ I₁ circuit₂ I₂).chal (fun x => H (.inr (.inr x))) p)
        (H (.inr (.inr p))) := by
  change S₂.charge Prod.fst Prod.snd W.2 p _ _ = _
  congr 1
  funext i
  exact prefix_two circuit₁ I₁ circuit₂ I₂ H p i

/-- Finite witness search in the two fixed committed lists. The result
satisfies both actual circuits and agrees on the common message. -/
noncomputable def extract (W : I₁.layer.Oracle × I₂.layer.Oracle)
    (proof : Proof Key C Public circuit₁ I₁ circuit₂ I₂) :
    Option ((Counting.tupleCounts I₁).Index × (Counting.tupleCounts I₂).Index) :=
  if h : ∃ g₁ g₂, S₁.Good proof.context W.1 g₁ ∧
      S₂.Good (proof.context,selectedOne circuit₁ I₁ circuit₂ I₂ proof) W.2 g₂ ∧ M.commonOne g₁ = M.commonTwo g₂ then
    some (h.choose,h.choose_spec.choose)
  else none

theorem extract_none_iff (W : I₁.layer.Oracle × I₂.layer.Oracle)
    (proof : Proof Key C Public circuit₁ I₁ circuit₂ I₂) :
    extract circuit₁ I₁ circuit₂ I₂ S₁ S₂ M W proof = none ↔
      ¬ ∃ g₁ g₂, S₁.Good proof.context W.1 g₁ ∧
        S₂.Good (proof.context,selectedOne circuit₁ I₁ circuit₂ I₂ proof) W.2 g₂ ∧ M.commonOne g₁ = M.commonTwo g₂ := by
  unfold extract
  split_ifs with h
  · simp only [h, not_true_eq_false]
  · simp only [h, not_false_eq_true]

theorem extract_valid (W : I₁.layer.Oracle × I₂.layer.Oracle)
    (proof : Proof Key C Public circuit₁ I₁ circuit₂ I₂)
    (pair : (Counting.tupleCounts I₁).Index × (Counting.tupleCounts I₂).Index)
    (h : extract circuit₁ I₁ circuit₂ I₂ S₁ S₂ M W proof = some pair) :
    S₁.Good proof.context W.1 pair.1 ∧
      S₂.Good (proof.context,selectedOne circuit₁ I₁ circuit₂ I₂ proof) W.2 pair.2 ∧
        M.commonOne pair.1 = M.commonTwo pair.2 := by
  unfold extract at h
  split_ifs at h with hex
  · have he := Option.some.inj h
    rw [← he]
    exact hex.choose_spec.choose_spec

noncomputable def totalOne (W : I₁.layer.Oracle × I₂.layer.Oracle)
    (H : Domain Key C Public circuit₁ I₁ circuit₂ I₂ → C)
    (proof : Proof Key C Public circuit₁ I₁ circuit₂ I₂) : ℚ :=
  ∑ i : Fin (Replay.slots circuit₁+2),
    let p := GradedReplay.hashInput circuit₁ I₁ Prod.fst Prod.snd (selectedOne circuit₁ I₁ circuit₂ I₂ proof) i.val
    S₁.charge Prod.fst Prod.snd W.1 p ((pointsOne circuit₁ I₁).chal (fun x => H (.inr (.inl x))) p)
      (H (.inr (.inl p)))

noncomputable def totalTwo (W : I₁.layer.Oracle × I₂.layer.Oracle)
    (H : Domain Key C Public circuit₁ I₁ circuit₂ I₂ → C)
    (proof : Proof Key C Public circuit₁ I₁ circuit₂ I₂) : ℚ :=
  ∑ i : Fin (Replay.slots circuit₂+2),
    let p := GradedReplay.hashInput circuit₂ I₂ Prod.fst Prod.snd (selectedTwo circuit₁ I₁ circuit₂ I₂ proof) i.val
    S₂.charge Prod.fst Prod.snd W.2 p ((pointsTwo circuit₁ I₁ circuit₂ I₂).chal (fun x => H (.inr (.inr x))) p)
      (H (.inr (.inr p)))

theorem totalOne_nonneg (W : I₁.layer.Oracle × I₂.layer.Oracle)
    (H : Domain Key C Public circuit₁ I₁ circuit₂ I₂ → C)
    (proof : Proof Key C Public circuit₁ I₁ circuit₂ I₂) :
    0 ≤ totalOne circuit₁ I₁ circuit₂ I₂ S₁ W H proof :=
  sum_nonneg (fun _ _ => S₁.charge_nonneg Prod.fst Prod.snd W.1 _ _ _)

theorem totalTwo_nonneg (W : I₁.layer.Oracle × I₂.layer.Oracle)
    (H : Domain Key C Public circuit₁ I₁ circuit₂ I₂ → C)
    (proof : Proof Key C Public circuit₁ I₁ circuit₂ I₂) :
    0 ≤ totalTwo circuit₁ I₁ circuit₂ I₂ S₂ W H proof :=
  sum_nonneg (fun _ _ => S₂.charge_nonneg Prod.fst Prod.snd W.2 _ _ _)

theorem sum_charge (W : I₁.layer.Oracle × I₂.layer.Oracle)
    (H : Domain Key C Public circuit₁ I₁ circuit₂ I₂ → C)
    (proof : Proof Key C Public circuit₁ I₁ circuit₂ I₂) :
    (∑ i : Fin (1+(Replay.slots circuit₁+2)+(Replay.slots circuit₂+2)),
      let p := hashInput circuit₁ I₁ circuit₂ I₂ proof i.val
      charge circuit₁ I₁ circuit₂ I₂ S₁ S₂ M W p ((points circuit₁ I₁ circuit₂ I₂).chal H p) (H p)) =
    RecursivePolygero.indicator (M.Bad (Counting.committedCandidates I₁ W.1 S₁.cutoff)
      (Counting.committedCandidates I₂ W.2 S₂.cutoff) (H (.inl proof.context.1))) +
      totalOne circuit₁ I₁ circuit₂ I₂ S₁ W H proof + totalTwo circuit₁ I₁ circuit₂ I₂ S₂ W H proof := by
  let f := fun p : Domain Key C Public circuit₁ I₁ circuit₂ I₂ =>
    charge circuit₁ I₁ circuit₂ I₂ S₁ S₂ M W p ((points circuit₁ I₁ circuit₂ I₂).chal H p) (H p)
  change (∑ i : Fin (1+(Replay.slots circuit₁+2)+(Replay.slots circuit₂+2)),
    f (hashInput circuit₁ I₁ circuit₂ I₂ proof i.val)) = _
  rw [TwoFieldReplay.sum_hashInput circuit₁ I₁ circuit₂ I₂ proof f]
  simp only [f, charge_one_eq, charge_two_eq, totalOne, totalTwo]
  rfl

/-- The separate private MAC blinds enter through the two affine row
identities. No equality between those blinds is assumed. -/
theorem path_charge_ge_one (W : I₁.layer.Oracle × I₂.layer.Oracle)
    (H : Domain Key C Public circuit₁ I₁ circuit₂ I₂ → C)
    (proof : Proof Key C Public circuit₁ I₁ circuit₂ I₂)
    (hkey : proof.context.2.1 = H (.inl proof.context.1))
    (hacceptOne : S₁.Accepts Prod.fst Prod.snd W.1 (fun x => H (.inr (.inl x)))
      (selectedOne circuit₁ I₁ circuit₂ I₂ proof))
    (hacceptTwo : S₂.Accepts Prod.fst Prod.snd W.2 (fun x => H (.inr (.inr x)))
      (selectedTwo circuit₁ I₁ circuit₂ I₂ proof))
    (tag : Fin blocks → Fmac)
    (hrowOne : ∀ g, S₁.Good proof.context W.1 g →
      M.macOne g (M.decode proof.context.2.1) = tag)
    (hrowTwo : ∀ g, S₂.Good (proof.context,selectedOne circuit₁ I₁ circuit₂ I₂ proof) W.2 g →
      M.macTwo g (M.decode proof.context.2.1) = tag)
    (hbad : ¬ ∃ g₁ g₂, S₁.Good proof.context W.1 g₁ ∧
      S₂.Good (proof.context,selectedOne circuit₁ I₁ circuit₂ I₂ proof) W.2 g₂ ∧ M.commonOne g₁ = M.commonTwo g₂) :
    1 ≤ ∑ i : Fin (1+(Replay.slots circuit₁+2)+(Replay.slots circuit₂+2)),
      let p := hashInput circuit₁ I₁ circuit₂ I₂ proof i.val
      charge circuit₁ I₁ circuit₂ I₂ S₁ S₂ M W p ((points circuit₁ I₁ circuit₂ I₂).chal H p) (H p) := by
  rw [sum_charge]
  have hzeroOne := totalOne_nonneg circuit₁ I₁ circuit₂ I₂ S₁ W H proof
  have hzeroTwo := totalTwo_nonneg circuit₁ I₁ circuit₂ I₂ S₂ W H proof
  have hzeroKey := RecursivePolygero.indicator_nonneg (M.Bad
    (Counting.committedCandidates I₁ W.1 S₁.cutoff) (Counting.committedCandidates I₂ W.2 S₂.cutoff)
    (H (.inl proof.context.1)))
  by_cases hone : ∃ g, S₁.Good proof.context W.1 g
  · by_cases htwo : ∃ g, S₂.Good (proof.context,selectedOne circuit₁ I₁ circuit₂ I₂ proof) W.2 g
    · obtain ⟨g₁,hg₁⟩ := hone
      obtain ⟨g₂,hg₂⟩ := htwo
      have hne : M.commonOne g₁ ≠ M.commonTwo g₂ := fun he => hbad ⟨g₁,g₂,hg₁,hg₂,he⟩
      have hmac : M.Bad (Counting.committedCandidates I₁ W.1 S₁.cutoff)
          (Counting.committedCandidates I₂ W.2 S₂.cutoff) (H (.inl proof.context.1)) := by
        rw [← hkey]
        exact ⟨g₁,hg₁.1,g₂,hg₂.1,hne,(hrowOne g₁ hg₁).trans (hrowTwo g₂ hg₂).symm⟩
      rw [show RecursivePolygero.indicator (M.Bad (Counting.committedCandidates I₁ W.1 S₁.cutoff)
          (Counting.committedCandidates I₂ W.2 S₂.cutoff) (H (.inl proof.context.1))) = 1 by
        simp only [RecursivePolygero.indicator, if_pos hmac]]
      linarith
    · have hp : 1 ≤ totalTwo circuit₁ I₁ circuit₂ I₂ S₂ W H proof :=
        S₂.path_charge_ge_one Prod.fst Prod.snd W.2 (fun x => H (.inr (.inr x)))
          (selectedTwo circuit₁ I₁ circuit₂ I₂ proof) htwo hacceptTwo
      linarith
  · have hp : 1 ≤ totalOne circuit₁ I₁ circuit₂ I₂ S₁ W H proof :=
      S₁.path_charge_ge_one Prod.fst Prod.snd W.1 (fun x => H (.inr (.inl x)))
        (selectedOne circuit₁ I₁ circuit₂ I₂ proof) hone hacceptOne
    linarith

end TwoFieldPotential
end LfzkV2
