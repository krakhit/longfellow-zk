import LfzkV2.Schedule
import LfzkV2.RoundReplay

/-!
# Exact algebraic tests at the V2 challenge roles

This presentation follows the block schedule of `Replay.readFrom`. The
assertion block is tested before it changes the effective tensor; each round
uses the prefix-local sumcheck test, and the combination uses the two claims
already transmitted. The suffix carries the verifier's actual updated weights
and incoming claim.
-/

namespace LfzkV2.Replay

open SumcheckV2 ChallengeBlocks

variable {F Pad Slot C : Type} [Field F]

def clearMessages {n : ℕ} (plan : LayerPads Pad Slot n) (payload : LayerPayload F n) (pads : Pad → F) :
    Fin n → RoundPoly F :=
  fun i => unmask (payload.rounds i) ⟨pads (plan.round0 i),pads (plan.round1 i)⟩

theorem read_clearMessages (decode : (n : ℕ) → C → Fin n → F)
    {out mid input a : ℕ} (body : CircuitLayer (Cube out) (Cube mid) (Fin a) F)
    (rest : Circuit F mid input) (plan : PadPlan (Pad := Pad) (Slot := Slot) (.layer a body rest))
    (payload : Payload (.layer a body rest)) (answers : ℕ → C) (start : ℕ) (pads : Pad → F) :
    (readFrom decode (.layer a body rest) plan payload answers start).1.transcript.clearRounds pads =
      List.ofFn (clearMessages plan.1 payload.1 pads) := by
  simp only [readFrom, LayerMessages.transcript, LayerTranscript.clearRounds, List.map_ofFn]
  rfl

noncomputable def layerData (decode : (n : ℕ) → C → Fin n → F) :
    {out input : ℕ} → (circuit : Circuit F out input) →
    PadPlan (Pad := Pad) (Slot := Slot) circuit → Payload circuit → (ℕ → C) → ℕ →
    (Cube input → F) → (Cube out → F) → (Pad → F) → F →
    (role : LayerRole circuit) → Data F (LayerRole.kind circuit role)
  | _, _, .input, _, _, _, _, _, _, _, _, role => Fin.elim0 role
  | _, _, .layer (mid := mid) a body rest, plan, payload, answers, start, w, weights, pads, claim, role =>
      let ml := (readFrom decode (.layer a body rest) plan payload answers start).1
      let wires := rest.eval w
      let K := body.effective weights ml.beta
      match role with
      | .inl _ => (dot weights (body.outputs wires), claim, body.residuals wires)
      | .inr (.inl i) => RoundReplay.dataAt (bindRight K wires) wires
          (clearMessages plan.1 payload.1 pads) claim i (SumcheckV1.extract_prefix ml.point i)
      | .inr (.inr (.inl _)) =>
          ⟨evaluate wires ml.point, evaluate (bindRight K wires) ml.point,
            ml.transcript.clearA pads, ml.transcript.clearB pads⟩
      | .inr (.inr (.inr role)) =>
          layerData decode rest plan.2 payload.2 answers (start + vectorSlots a + mid + 1) w
            (nextWeights K (monomialWeights ml.point) ml.alpha) pads
            (ml.transcript.clearA pads + ml.alpha * ml.transcript.clearB pads) role

theorem layerData_valid (decode : (n : ℕ) → C → Fin n → F)
    {out input : ℕ} (circuit : Circuit F out input)
    (plan : PadPlan (Pad := Pad) (Slot := Slot) circuit) (payload : Payload circuit)
    (answers : ℕ → C) (start : ℕ) (w : Cube input → F) (weights : Cube out → F)
    (pads : Pad → F) (claim : F) (role : LayerRole circuit) :
    Data.Valid (layerData decode circuit plan payload answers start w weights pads claim role) := by
  induction circuit generalizing start claim with
  | input => exact Fin.elim0 role
  | layer a body rest ih =>
      rcases role with i | i | i | role
      · trivial
      · exact RoundReplay.dataAt_valid _ _ _ _ _ _
      · trivial
      · apply ih

/-- The asserted-circuit soundness reduction selects one actual block test
on this schedule, with its actual decoded answer. -/
theorem layer_bad_of_assertedBad (decode : (n : ℕ) → C → Fin n → F)
    {out input : ℕ} (circuit : Circuit F out input)
    (plan : PadPlan (Pad := Pad) (Slot := Slot) circuit) (payload : Payload circuit)
    (answers : ℕ → C) (start : ℕ) (w : Cube input → F) (weights : Cube out → F)
    (pads : Pad → F) (claim : F)
    (hbad : AssertedBad pads claim (circuit.execution
      (readFrom decode circuit plan payload answers start) w weights)) :
    ∃ role : LayerRole circuit,
      Data.Bad (layerData decode circuit plan payload answers start w weights pads claim role)
        (decode (LayerRole.kind circuit role).dimension (answers (start + layerSlot circuit role))) := by
  induction circuit generalizing start claim with
  | input => exact hbad.elim
  | layer a body rest ih =>
      rcases hbad with hassert | hlayer | hrest
      · have ha : a ≠ 0 := by
          obtain ⟨i,_⟩ := hassert
          exact Nat.ne_zero_of_lt i.isLt
        let i : Fin (vectorSlots a) := ⟨0,by simp [vectorSlots,ha]⟩
        exact ⟨.inl i,hassert⟩
      · rcases hlayer with hround | hcombine
        · rw [read_clearMessages] at hround
          obtain ⟨i,hi⟩ := (RoundReplay.round_bad_iff _ _ _ _ _).1 hround
          refine ⟨.inr (.inl i), ?_⟩
          simp only [layerData, LayerRole.kind, layerSlot_round, Data.Bad, readFrom,
            CircuitLayer.model, ChallengeTest.Bad, Kind.dimension, Nat.add_assoc] at hi ⊢
          convert! hi using 1
        · refine ⟨.inr (.inr (.inl 0)), ?_⟩
          simp only [layerData, LayerRole.kind, layerSlot_combine, Data.Bad, readFrom,
            CircuitLayer.model, LayerMessages.transcript, Kind.dimension, Nat.add_assoc] at hcombine ⊢
          convert! hcombine using 1
      · obtain ⟨role,hrole⟩ := ih plan.2 payload.2 _ _ _ _ hrest
        refine ⟨.inr (.inr (.inr role)), ?_⟩
        simpa only [layerData, LayerRole.kind, layerSlot_there, readFrom,
          LayerMessages.transcript, Nat.add_assoc] using hrole

noncomputable def semanticData (decode : (n : ℕ) → C → Fin n → F)
    {out input : ℕ} (circuit : Circuit F out input)
    (plan : PadPlan (Pad := Pad) (Slot := Slot) circuit) (payload : Payload circuit)
    (answers : ℕ → C) (w : Cube input → F) (pads : Pad → F) :
    (role : Role circuit) → Data F (roleKind circuit role)
  | .inl _ => circuit.eval w
  | .inr role => layerData decode circuit plan payload answers (vectorSlots out) w
      (monomialWeights (outputPoint decode out answers)) pads 0 role

theorem semanticData_valid (decode : (n : ℕ) → C → Fin n → F)
    {out input : ℕ} (circuit : Circuit F out input)
    (plan : PadPlan (Pad := Pad) (Slot := Slot) circuit) (payload : Payload circuit)
    (answers : ℕ → C) (w : Cube input → F) (pads : Pad → F) (role : Role circuit) :
    Data.Valid (semanticData decode circuit plan payload answers w pads role) := by
  cases role with
  | inl _ => trivial
  | inr role => exact layerData_valid _ _ _ _ _ _ _ _ _ _ _

theorem semantic_bad_of_accepts (decode : (n : ℕ) → C → Fin n → F)
    {out input : ℕ} (circuit : Circuit F out input)
    (plan : PadPlan (Pad := Pad) (Slot := Slot) circuit) (payload : Payload circuit)
    (answers : ℕ → C) (w : Cube input → F) (pads : Pad → F)
    (hfalse : ¬ circuit.Satisfies w)
    (haccept : ClearAccepts pads 0 (circuit.proof (read decode circuit plan payload answers))
      (dot (circuit.inputWeights (read decode circuit plan payload answers)
        (monomialWeights (outputPoint decode out answers))) w)) :
    ∃ role : Role circuit,
      Data.Bad (semanticData decode circuit plan payload answers w pads role)
        (decode (roleKind circuit role).dimension (answers (roleEquiv circuit role).val)) := by
  rcases circuit.soundness_reduction _ w (outputPoint decode out answers) pads hfalse haccept with houtput | hlayer
  · have hout : out ≠ 0 := by
      intro h
      subst out
      exact houtput.elim
    let i : Fin (vectorSlots out) := ⟨0,by simp [vectorSlots,hout]⟩
    exact ⟨.inl i,houtput⟩
  · obtain ⟨role,hrole⟩ := layer_bad_of_assertedBad decode circuit plan payload answers
      (vectorSlots out) w _ pads 0 hlayer
    exact ⟨.inr role,hrole⟩

end LfzkV2.Replay
