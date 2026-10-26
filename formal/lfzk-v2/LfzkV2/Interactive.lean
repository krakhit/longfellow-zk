import LfzkV2.Nizk
import polygero.Local.Probability

/-!
# Composition with the public-coin Polygero backend

The existing random-target envelope handles a statement chosen by earlier
frontend randomness. It does not require a union bound over all polynomial
tuples. The committed oracle is fixed before that randomness, and the backend
coins and opening query are independently uniform. This is an interactive
composition theorem, not a Fiat--Shamir conversion of the backend.
-/

namespace LfzkV2.Interactive

open SumcheckV2 RecursivePolygero RecursivePolygero.Counting
open RecursivePolygero.ProfileAnalysis

variable {F Pad Slot Z : Type} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Z] [Nonempty Z]
variable {out input nPublic nPrivate : ℕ}

/-- A bound on each fixed decoded witness's frontend bad tests composes with
the proved Polygero random-target envelope. The payload may depend on all
frontend randomness and the backend coin, but not on the opening query. -/
theorem soundness_le
    (circuit : Circuit F out input)
    (index : (Fin nPublic ⊕ Fin nPrivate) ↪ Cube input)
    (publicInputs : Fin nPublic → F) (privateCoordinate : Fin nPrivate → Slot)
    (coordinate : Pad → Slot)
    (I : Instance F) (parameters : HahnSystemCertificate I)
    (view : Z → Reconstruction circuit Pad Slot)
    (primary : Slot → Fin I.nw × Fin I.q)
    (product : (z : Z) → Fin (view z).constraints.layers.length → Fin I.nq × Fin I.q)
    (eqns : (z : Z) → I.Equations ≃ Backend.Equation
      ((view z).rows index publicInputs privateCoordinate coordinate).length
      (view z).constraints.layers.length)
    (oracle : I.layer.Oracle)
    (payload : Z → I.layer.Coin → I.layer.Payload)
    (r : ℚ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hfalse : ∀ privateInputs : Fin nPrivate → F,
      ¬ circuit.Satisfies (zeroExtend index (Sum.elim publicInputs privateInputs)))
    (hfrontend : ∀ g : (tupleCounts I).Index,
      mean (fun z => indicator
        (((view z).tests index publicInputs privateCoordinate coordinate
          (Backend.read ((tupleCounts I).witness g) ∘ Backend.linearAddress primary)).Bad)) ≤ r) :
    let statement := fun z => Backend.statement
      (Backend.rows ((view z).rows index publicInputs privateCoordinate coordinate)
        (view z).constraints coordinate primary (product z) ∘ eqns z)
    mean (fun z => mean (fun coin => mean (fun query =>
      indicator (I.layer.verify (statement z) oracle coin (payload z coin) query)))) ≤
        parameters.error + (1 - parameters.error) * r := by
  intro statement
  let D := fun z (g : (tupleCounts I).Index) =>
    ((view z).tests index publicInputs privateCoordinate coordinate
      (Backend.read ((tupleCounts I).witness g) ∘ Backend.linearAddress primary)).Bad
  have htarget (z : Z) (coin : I.layer.Coin) :
      outputHit (D z) (scanRecoverAt I (statement z) oracle coin (payload z coin)) := by
    cases he : scanRecoverAt I (statement z) oracle coin (payload z coin) with
    | none => trivial
    | some g =>
        exact (view z).accepts_false index publicInputs privateCoordinate coordinate _ hfalse
          ((view z).decoded_accepts index publicInputs privateCoordinate coordinate
            I primary (product z) (eqns z) oracle coin (payload z coin) g he)
  have hlocal (z : Z) (coin : I.layer.Coin) :=
    family_response_mean I parameters.toProfileParameters (statement z) oracle
      parameters.threshold parameters.columnFloor_le parameters.threshold_lt_one.le
      (D z) coin (payload z coin)
  have hbound := mean_mono fun z => mean_mono fun coin => hlocal z coin
  simp only [htarget, and_true] at hbound
  exact hbound.trans (localEnvelope_mean_of_hahn I parameters statement oracle r
    hr0 hr1 D hfrontend)

section FiatShamirFrontend

variable {Q Out Key Context : Type} [Fintype Q] [DecidableEq Q] {N L : ℕ}

/-- Adaptive Fiat–Shamir frontend tests compose with fresh public-coin backend
challenges. The random-target envelope uses a separate bound for each fixed
witness, so no cardinality factor for all polynomial tuples is charged. The
frontend reconstruction and backend payload may depend on the frontend oracle. -/
theorem soundness_le_fiatShamir_frontend
    (circuit : Circuit F out input)
    (index : (Fin nPublic ⊕ Fin nPrivate) ↪ Cube input)
    (publicInputs : Fin nPublic → F) (privateCoordinate : Fin nPrivate → Slot)
    (coordinate : Pad → Slot)
    (I : Instance F) (parameters : HahnSystemCertificate I)
    (setup : FiatShamir.Setup F Q Out Key Context (tupleCounts I).Index N L)
    (view : (Q → F) → Reconstruction circuit Pad Slot)
    (primary : Slot → Fin I.nw × Fin I.q)
    (product : (H : Q → F) → Fin (view H).constraints.layers.length → Fin I.nq × Fin I.q)
    (eqns : (H : Q → F) → I.Equations ≃ Backend.Equation
      ((view H).rows index publicInputs privateCoordinate coordinate).length
      (view H).constraints.layers.length)
    (oracle : I.layer.Oracle)
    (payload : (Q → F) → I.layer.Coin → I.layer.Payload)
    (hfalse : ∀ privateInputs : Fin nPrivate → F,
      ¬ circuit.Satisfies (zeroExtend index (Sum.elim publicInputs privateInputs)))
    (hcover : ∀ H g, setup.Covers H g
      ((view H).tests index publicInputs privateCoordinate coordinate
        (Backend.read ((tupleCounts I).witness g) ∘ Backend.linearAddress primary)))
    (maxBudget : ℕ) (hmax : ∀ x, setup.budget x ≤ maxBudget)
    (slotBudget : Fin L → ℕ)
    (hslot : ∀ result i, setup.budget (setup.hashInput result i.val) ≤ slotBudget i) :
    let statement := fun H => Backend.statement
      (Backend.rows ((view H).rows index publicInputs privateCoordinate coordinate)
        (view H).constraints coordinate primary (product H) ∘ eqns H)
    mean (fun H => mean (fun coin => mean (fun query =>
      indicator (I.layer.verify (statement H) oracle coin (payload H coin) query)))) ≤
        parameters.error + (1 - parameters.error) *
          min 1 ((N * maxBudget + ∑ i, slotBudget i : ℕ) / (Fintype.card F : ℚ)) := by
  let r : ℚ := (N * maxBudget + ∑ i, slotBudget i : ℕ) / (Fintype.card F : ℚ)
  apply soundness_le circuit index publicInputs privateCoordinate coordinate I parameters
    view primary product eqns oracle payload (min 1 r)
    (by dsimp [r]; positivity) (min_le_left _ _) hfalse
  intro g
  apply le_min
  · apply mean_le
    intro H
    unfold indicator
    split_ifs <;> norm_num
  · have h := setup.fixed_candidate_soundness_le g maxBudget hmax slotBudget hslot
      (fun H => ((view H).tests index publicInputs privateCoordinate coordinate
        (Backend.read ((tupleCounts I).witness g) ∘ Backend.linearAddress primary)).Bad)
      (by intro H hH; exact ⟨_, hcover H g, hH⟩)
    simpa only [mean_indicator, Fintype.card_fun, Nat.cast_pow, r, Nat.cast_add,
      Nat.cast_mul] using h

end FiatShamirFrontend

end LfzkV2.Interactive
