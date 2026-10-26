import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Adaptive message masking

A clear response may depend on the private witness and the preceding public
transcript. Its fresh pad is subtracted before the public transition, which
can include Fiat--Shamir sampling. The triangular map from independent pads to
masked messages is a bijection for each fixed initial state. Instantiating this
lemma for V2 still requires handling the earlier commitment, which depends on
the pads. It does not establish privacy of the actual joint protocol view.
-/

namespace LfzkV2.Masking

open Classical

variable {F State : Type} [Field F]

def visible (response : State → F) (next : State → F → State) :
    {n : ℕ} → State → (Fin n → F) → Fin n → F
  | 0, _, _ => Fin.elim0
  | _ + 1, state, pads =>
      let message := response state - pads 0
      Fin.cons message (visible response next (next state message) (fun i => pads i.succ))

def recover (response : State → F) (next : State → F → State) :
    {n : ℕ} → State → (Fin n → F) → Fin n → F
  | 0, _, _ => Fin.elim0
  | _ + 1, state, messages =>
      Fin.cons (response state - messages 0)
        (recover response next (next state (messages 0)) (fun i => messages i.succ))

theorem recover_visible (response : State → F) (next : State → F → State)
    {n : ℕ} (state : State) (pads : Fin n → F) :
    recover response next state (visible response next state pads) = pads := by
  induction n generalizing state with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
      simp only [visible, recover, Fin.cons_zero, Fin.cons_succ, sub_sub_cancel, ih]
      exact Fin.cons_self_tail pads

theorem visible_recover (response : State → F) (next : State → F → State)
    {n : ℕ} (state : State) (messages : Fin n → F) :
    visible response next state (recover response next state messages) = messages := by
  induction n generalizing state with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
      simp only [recover, visible, Fin.cons_zero, Fin.cons_succ, sub_sub_cancel, ih]
      exact Fin.cons_self_tail messages

def equiv (response : State → F) (next : State → F → State) {n : ℕ} (state : State) :
    (Fin n → F) ≃ (Fin n → F) where
  toFun := visible response next state
  invFun := recover response next state
  left_inv := recover_visible response next state
  right_inv := visible_recover response next state

/-- Every public transcript has exactly one pad preimage, even with adaptive responses. -/
theorem uniform_fiber [Fintype F] (response : State → F) (next : State → F → State)
    {n : ℕ} (state : State) (messages : Fin n → F) :
    (Finset.univ.filter fun pads => visible response next state pads = messages).card = 1 := by
  classical
  have heq : (Finset.univ.filter fun pads => visible response next state pads = messages) =
      {recover response next state messages} := by
    ext pads
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact (equiv response next state).apply_eq_iff_eq_symm_apply
  rw [heq, Finset.card_singleton]

end LfzkV2.Masking
