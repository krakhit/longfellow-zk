import LfzkV2.OracleSampling

/-!
# Message-prefix Fiat–Shamir points

A hash point carries its commitment key, challenge position, and the prover
messages through that position. Earlier challenge answers are recomputed at
their own prefix points. They are not included in later hash inputs.
-/

namespace LfzkV2.Transcript

open Bcs.TotalOracle
open scoped Classical

variable {Key Msg C Context Out : Type} {L : ℕ}

abbrev Point (Key Msg : Type) (L : ℕ) :=
  Key × (i : Fin L) × (Fin (i.val+1) → Msg)

def pointAt (key : Key) (messages : ℕ → Msg) (i : Fin L) : Point Key Msg L :=
  (key, ⟨i, fun j => messages j.val⟩)

def ancestor (point : Point Key Msg L) (j : ℕ) : Point Key Msg L :=
  if h : j < point.2.1.val then
    (point.1, ⟨⟨j, h.trans point.2.1.isLt⟩,
      fun k => point.2.2 ⟨k.val, Nat.lt_trans k.isLt (Nat.succ_lt_succ h)⟩⟩)
  else point

theorem ancestor_ne (point : Point Key Msg L) (j : ℕ) (hj : j < point.2.1.val) :
    ancestor point j ≠ point := by
  rw [ancestor, dif_pos hj]
  intro h
  exact (Nat.ne_of_lt hj) (congrArg (fun p : Point Key Msg L => p.2.1.val) h)

def points : PrefixPoints (Point Key Msg L) where
  slot point := point.2.1.val
  anc := ancestor
  anc_ne := ancestor_ne

theorem ancestor_at (key : Key) (messages : ℕ → Msg) (i : Fin L) (j : Fin i.val) :
    ancestor (pointAt key messages i) j.val = pointAt key messages ⟨j.val, j.isLt.trans i.isLt⟩ := by
  simp only [ancestor, pointAt, dif_pos j.isLt]

theorem prefix_answers (H : Point Key Msg L → C) (key : Key)
    (messages : ℕ → Msg) (i : Fin L) :
    points.chal H (pointAt key messages i) =
      fun j : Fin i.val => H (pointAt key messages ⟨j.val, j.isLt.trans i.isLt⟩) := by
  funext j
  exact congrArg H (ancestor_at key messages i j)

theorem at_injective (key : Key) (messages : ℕ → Msg) :
    Function.Injective (pointAt (L := L) key messages) := by
  intro i j h
  exact Fin.ext (congrArg (fun p : Point Key Msg L => p.2.1.val) h)

/-- The point at a challenge reads precisely the message prefix through that
challenge, including the current prover message. -/
theorem at_eq_of_message_prefix (key : Key) (first second : ℕ → Msg) (i : Fin L)
    (hprefix : ∀ j, j ≤ i.val → first j = second j) :
    pointAt key first i = pointAt key second i := by
  unfold pointAt
  refine Prod.ext rfl ?_
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext j
  exact hprefix j.val (Nat.lt_succ_iff.mp j.isLt)

/-- Cut-trace commitment contexts are fixed when all answers in the named
commitment fiber are resampled. This implies the single-coordinate condition
required by the frontend oracle theorem. -/
theorem context_off_of_fiber
    (context : (Point Key Msg L → C) → Key → Context)
    (hcontext : ∀ key H H',
      (∀ p : Point Key Msg L, p.1 ≠ key → H p = H' p) → context H key = context H' key)
    (H H' : Point Key Msg L → C) (point : Point Key Msg L)
    (hoff : AgreeOff point H H') : context H' point.1 = context H point.1 := by
  apply hcontext
  intro p hp
  exact (hoff p (fun h => hp (h ▸ rfl))).symm

end LfzkV2.Transcript
