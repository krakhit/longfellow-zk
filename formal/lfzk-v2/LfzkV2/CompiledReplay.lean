import LfzkV2.FrontendFS
import LfzkV2.Nizk

/-! The actual replay supplies the public reconstruction consumed by the
Polygero compiler. Its decoded acceptance is exactly frontend acceptance. -/

namespace LfzkV2.Replay

open SumcheckV2

variable {F C Pad Slot Key Other : Type} [Field F] {out input : ℕ}

noncomputable def reconstructionFromAnswers (decode : (n : ℕ) → C → Fin n → F)
    (circuit : Circuit F out input) (plan : PadPlan (Pad := Pad) (Slot := Slot) circuit)
    (payload : Payload circuit) (answers : ℕ → C) :
    Reconstruction circuit Pad Slot :=
  let h := read_constraints decode circuit plan payload answers
  ⟨read decode circuit plan payload answers, outputPoint decode out answers, h.choose, h.choose_spec.1⟩

noncomputable def reconstruction (decode : (n : ℕ) → C → Fin n → F)
    (circuit : Circuit F out input) (plan : PadPlan (Pad := Pad) (Slot := Slot) circuit)
    (key : Key) (payload : Payload circuit) (H : Query Key F circuit Other → C) :
    Reconstruction circuit Pad Slot :=
  reconstructionFromAnswers decode circuit plan payload (fun j => H (.inl (hashInput circuit key payload j)))

theorem reconstruction_accepts {nPublic nPrivate : ℕ}
    (decode : (n : ℕ) → C → Fin n → F)
    (circuit : Circuit F out input) (plan : PadPlan (Pad := Pad) (Slot := Slot) circuit)
    (key : Key) (payload : Payload circuit) (H : Query Key F circuit Other → C)
    (index : (Fin nPublic ⊕ Fin nPrivate) ↪ Cube input)
    (publicInputs : Fin nPublic → F) (privateCoordinate : Fin nPrivate → Slot)
    (coordinate : Pad → Slot) (witness : Slot → F)
    (haccept : (reconstruction decode circuit plan key payload H).Accepts
      index publicInputs privateCoordinate coordinate witness) :
    oracleAccepts circuit plan decode key payload H
      (circuitInputs index publicInputs privateCoordinate witness) (witness ∘ coordinate) := by
  let v := reconstruction decode circuit plan key payload H
  change ClearAccepts _ _ _ _
  rw [input_sum]
  exact (compiled_iff_clear (circuit.proof v.messages) v.constraints v.built
    coordinate privateCoordinate _ publicInputs _ witness haccept.1).mp haccept.2

theorem reconstruction_eq_of_answers
    (decode : (n : ℕ) → C → Fin n → F)
    (circuit : Circuit F out input) (plan : PadPlan (Pad := Pad) (Slot := Slot) circuit)
    (key : Key) (payload : Payload circuit) (H H' : Query Key F circuit Other → C)
    (hanswers : ∀ j, H (.inl (hashInput circuit key payload j)) =
      H' (.inl (hashInput circuit key payload j))) :
    reconstruction decode circuit plan key payload H = reconstruction decode circuit plan key payload H' := by
  exact congrArg (reconstructionFromAnswers decode circuit plan payload) (funext hanswers)

omit [Field F] in
/-- A context fixed off each named point is also fixed when two points naming
the same key are jointly resampled. No independence premise is needed. -/
theorem context_eq_of_off_two {Q C Key Context : Type}
    (context : (Q → C) → Key → Context) (key : Q → Key)
    (context_off : ∀ H H' x, Bcs.TotalOracle.AgreeOff x H H' → context H' (key x) = context H (key x))
    (x y : Q) (hkey : key x = key y) (H H' : Q → C)
    (hoff : ∀ z, z ≠ x → z ≠ y → H z = H' z) : context H (key x) = context H' (key x) := by
  classical
  let middle := Function.update H x (H' x)
  have hx : Bcs.TotalOracle.AgreeOff x H middle := by
    intro z hzx
    simp [middle, hzx]
  have hy : Bcs.TotalOracle.AgreeOff y middle H' := by
    intro z hzy
    by_cases hzx : z = x
    · subst z
      simp [middle]
    · simpa [middle, hzx] using hoff z hzx hzy
  calc
    context H (key x) = context middle (key x) := (context_off H middle x hx).symm
    _ = context H' (key x) := by
      rw [hkey]
      exact (context_off middle H' y hy).symm

end LfzkV2.Replay
