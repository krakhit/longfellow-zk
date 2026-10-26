import LfzkV1.Mac

/-! V2's cross-field MAC: one verifier multiplier for all blocks and one
private additive pad per block. Soundness permits different fixed pads on
the two extracted sides. The hiding permutation acts on the additive pads. -/

namespace LfzkV2.Mac

open Finset
open scoped Classical

variable {F : Type} [Field F] {blocks : ℕ}

def tag (av : F) (ap message : Fin blocks → F) : Fin blocks → F :=
  fun j => av * message j + ap j

/-- Only the fixed-pair affine collision lemma is reused from V1. -/
theorem collision_card_le_one [Fintype F] [DecidableEq F]
    (ap ap' message message' : Fin blocks → F) (hne : message ≠ message') :
    (univ.filter fun av => tag av ap message = tag av ap' message').card ≤ 1 :=
  LfzkV1.Mac.macTag_collision_card_le_one ap ap' message message' hne

def blindEquiv (av : F) (message : Fin blocks → F) :
    (Fin blocks → F) ≃ (Fin blocks → F) where
  toFun ap := tag av ap message
  invFun t := fun j => t j - av * message j
  left_inv ap := by funext j; simp [tag]
  right_inv t := by funext j; simp [tag]

/-- A uniform additive pad gives an exactly uniform tag for every fixed
message and multiplier, including the zero multiplier. -/
theorem uniform_tag_card [Fintype F] (av : F) (message : Fin blocks → F)
    (E : (Fin blocks → F) → Prop) :
    (univ.filter fun ap => E (tag av ap message)).card = (univ.filter E).card := by
  classical
  simp only [Finset.card_filter]
  exact Fintype.sum_equiv (blindEquiv av message) _ _ (fun _ => rfl)

/-- The same permutation preserves arbitrary joint events with a sampled
state. The state may fix the message and multiplier independently of the
fresh pad. In the honest two-field execution, this one tag is shared. -/
theorem uniform_joint_tag_card {State : Type} [Fintype State] [Fintype F]
    (av : State → F) (message : State → Fin blocks → F)
    (E : State × (Fin blocks → F) → Prop) :
    (univ.filter fun p : State × (Fin blocks → F) =>
      E (p.1,tag (av p.1) p.2 (message p.1))).card = (univ.filter E).card := by
  classical
  let e : (State × (Fin blocks → F)) ≃ (State × (Fin blocks → F)) := {
    toFun p := (p.1,blindEquiv (av p.1) (message p.1) p.2)
    invFun p := (p.1,(blindEquiv (av p.1) (message p.1)).symm p.2)
    left_inv p := by simp
    right_inv p := by simp }
  simp only [Finset.card_filter]
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

end LfzkV2.Mac
