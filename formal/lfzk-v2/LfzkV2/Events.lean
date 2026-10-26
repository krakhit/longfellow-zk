import LfzkV2.Inputs

/-!
# Concrete challenge tests for a reconstructed V2 execution

These lists expose the exact data needed at each challenge. The Fiat--Shamir
interface links these values to prefix-only oracle points; it does not assume
that accepted false statements imply an oracle bad event.
-/

namespace LfzkV2

open SumcheckV2 Classical

variable {F Pad Slot : Type} [Field F]

inductive ChallengeTest (F : Type) [Field F] where
  | linear (offset slope : F)
  | output {n : ℕ} (table : Cube (n + 1) → F)
  | round (data : RoundData F)
  | combine (data : CombineData F)

namespace ChallengeTest

def Valid : ChallengeTest F → Prop
  | .round data => data.truth.natDegree ≤ 2
  | _ => True

def budget : ChallengeTest F → ℕ
  | .round _ => 2
  | _ => 1

def Bad : ChallengeTest F → F → Prop
  | .linear offset slope, z => BadLinear offset slope z
  | .output table, z => BadFold table z
  | .round data, z => BadRoundEvent data.truth data.message data.claim z
  | .combine data, z => BadCombineEvent data.trueA data.trueB data.claimA data.claimB z

theorem card_bad_le [Fintype F] [DecidableEq F] (test : ChallengeTest F) (hvalid : test.Valid) :
    (Finset.univ.filter test.Bad).card ≤ test.budget := by
  cases test with
  | linear offset slope => exact bad_linear_card offset slope
  | output table => exact bad_fold_card table
  | round data => exact bad_round_roots data.truth data.message data.claim hvalid
  | combine data => exact bad_combine_roots data.trueA data.trueB data.claimA data.claimB

theorem budget_le_two (test : ChallengeTest F) : test.budget ≤ 2 := by
  cases test <;> simp [budget]

end ChallengeTest

abbrev Tests (F : Type) [Field F] := List (ChallengeTest F × F)

def Tests.Bad (tests : Tests F) : Prop := ∃ test ∈ tests, test.1.Bad test.2
def Tests.Valid (tests : Tests F) : Prop := ∀ test ∈ tests, test.1.Valid

@[simp] theorem Tests.bad_append (left right : Tests F) :
    (left ++ right).Bad ↔ left.Bad ∨ right.Bad := by
  constructor
  · rintro ⟨test, hmem, hbad⟩
    rcases List.mem_append.mp hmem with hl | hr
    · exact Or.inl ⟨test, hl, hbad⟩
    · exact Or.inr ⟨test, hr, hbad⟩
  · rintro (⟨test, hmem, hbad⟩ | ⟨test, hmem, hbad⟩)
    · exact ⟨test, List.mem_append_left _ hmem, hbad⟩
    · exact ⟨test, List.mem_append_right _ hmem, hbad⟩

@[simp] theorem Tests.valid_append (left right : Tests F) :
    (left ++ right).Valid ↔ left.Valid ∧ right.Valid := List.forall_mem_append

@[simp] theorem Tests.bad_cons (test : ChallengeTest F × F) (tests : Tests F) :
    Tests.Bad (test :: tests) ↔ test.1.Bad test.2 ∨ tests.Bad := by
  constructor
  · rintro ⟨other, hmem, hbad⟩
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact Or.inl hbad
    · exact Or.inr ⟨other, hmem, hbad⟩
  · rintro (hbad | ⟨other, hmem, hbad⟩)
    · exact ⟨test, List.mem_cons_self, hbad⟩
    · exact ⟨other, List.mem_cons_of_mem _ hmem, hbad⟩

def outputTests : {n : ℕ} → (Cube n → F) → (Fin n → F) → Tests F
  | 0, _, _ => []
  | _ + 1, table, point => (.output table, point 0) ::
      outputTests (fold table (point 0)) (fun j => point j.succ)

theorem outputTests_bad {n : ℕ} (table : Cube n → F) (point : Fin n → F) :
    (outputTests table point).Bad ↔ OutputBad table point := by
  induction n with
  | zero => simp [outputTests, Tests.Bad, OutputBad]
  | succ n ih =>
      simp only [outputTests, Tests.bad_cons, ChallengeTest.Bad, OutputBad]
      exact or_congr_right (ih _ _)

theorem outputTests_valid {n : ℕ} (table : Cube n → F) (point : Fin n → F) :
    (outputTests table point).Valid := by
  induction n with
  | zero => simp [outputTests, Tests.Valid]
  | succ n ih =>
      simp only [outputTests, Tests.Valid, List.forall_mem_cons, ChallengeTest.Valid, true_and]
      exact ih _ _

def roundTests (claim : F) : List (Polynomial F) → List (RoundPoly F) → List F → Tests F
  | P :: Ps, m :: ms, z :: zs => (.round ⟨P, m, claim⟩, z) ::
      roundTests (check_round claim m z) Ps ms zs
  | _, _, _ => []

theorem roundTests_bad (claim : F) (Ps : List (Polynomial F)) (ms : List (RoundPoly F))
    (zs : List F) :
    (roundTests claim Ps ms zs).Bad ↔ multi_round_bad_event claim Ps ms zs := by
  induction ms generalizing claim Ps zs with
  | nil => cases Ps <;> cases zs <;> simp [roundTests, Tests.Bad, multi_round_bad_event]
  | cons m ms ih =>
      cases Ps with
      | nil => simp [roundTests, Tests.Bad, multi_round_bad_event]
      | cons P Ps =>
          cases zs with
          | nil => simp [roundTests, Tests.Bad, multi_round_bad_event]
          | cons z zs =>
              simp only [roundTests, Tests.bad_cons, ChallengeTest.Bad,
                multi_round_bad_event]
              exact or_congr_right (ih _ _ _)

theorem roundTests_valid (claim : F) (Ps : List (Polynomial F)) (ms : List (RoundPoly F))
    (zs : List F) (hdeg : ∀ P ∈ Ps, P.natDegree ≤ 2) :
    (roundTests claim Ps ms zs).Valid := by
  induction ms generalizing claim Ps zs with
  | nil => cases Ps <;> cases zs <;> simp [roundTests, Tests.Valid]
  | cons m ms ih =>
      cases Ps with
      | nil => simp [roundTests, Tests.Valid]
      | cons P Ps =>
          cases zs with
          | nil => simp [roundTests, Tests.Valid]
          | cons z zs =>
              change (∀ test ∈ (.round ⟨P, m, claim⟩, z) ::
                roundTests (check_round claim m z) Ps ms zs, test.1.Valid)
              rw [List.forall_mem_cons]
              exact ⟨hdeg P List.mem_cons_self,
                ih _ _ _ (fun Q hQ => hdeg Q (List.mem_cons_of_mem _ hQ))⟩

/-- Only the last nonzero residual can be needed by assertion reduction. Its
index is fixed by the witness before the assertion challenges are sampled. -/
noncomputable def assertionIndices (m : AssertedModel F) : Finset (Fin m.assertions) :=
  Finset.univ.filter fun i => m.residuals i ≠ 0 ∧ ∀ j, i < j → m.residuals j = 0

theorem assertionIndices_card_le_one (m : AssertedModel F) : (assertionIndices m).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  obtain ⟨hi, hilast⟩ := (Finset.mem_filter.mp hi).2
  obtain ⟨hj, hjlast⟩ := (Finset.mem_filter.mp hj).2
  rcases lt_trichotomy i j with hij | hij | hij
  · exact (hj (hilast j hij)).elim
  · exact hij
  · exact (hi (hjlast i hij)).elim

noncomputable def assertionTests (m : AssertedModel F) (claim : F) : Tests F :=
  (assertionIndices m).toList.map fun i =>
    (.linear (assertionOffset m.incoming claim m.beta m.residuals i) (m.residuals i), m.beta i)

theorem assertionTests_bad (m : AssertedModel F) (claim : F)
    (hbad : AssertionBad m.incoming claim m.beta m.residuals) :
    (assertionTests m claim).Bad := by
  obtain ⟨i, hlast, hi⟩ := hbad
  refine ⟨_, List.mem_map.mpr ⟨i, ?_, rfl⟩, hi⟩
  exact Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi.1, hlast⟩)

noncomputable def layerTests (m : LayerModel F) (t : LayerTranscript Pad Slot F)
    (pads : Pad → F) (claim : F) : Tests F :=
  roundTests claim (truePolys (bindRight m.kernel m.wires) m.wires m.point)
    (t.clearRounds pads) t.challenges ++
  [(.combine ⟨evaluate m.wires m.point, evaluate (bindRight m.kernel m.wires) m.point,
      t.clearA pads, t.clearB pads⟩, t.alpha)]

theorem layerTests_bad (m : LayerModel F) (t : LayerTranscript Pad Slot F)
    (pads : Pad → F) (claim : F) :
    (layerTests m t pads claim).Bad ↔ m.Bad t pads claim := by
  rw [layerTests, Tests.bad_append, roundTests_bad]
  simp [Tests.Bad, ChallengeTest.Bad, LayerModel.Bad]

theorem layerTests_valid (m : LayerModel F) (t : LayerTranscript Pad Slot F)
    (pads : Pad → F) (claim : F) : (layerTests m t pads claim).Valid := by
  rw [layerTests, Tests.valid_append]
  exact ⟨roundTests_valid _ _ _ _ (truePolys_degree _ _ _), by
    simp [Tests.Valid, ChallengeTest.Valid]⟩

noncomputable def traceTests (pads : Pad → F) (claim : F) : AssertedTrace Pad Slot F → Tests F
  | [] => []
  | (t, m) :: rest => assertionTests m claim ++ layerTests m.toLayerModel t pads claim ++
      traceTests pads (t.clearA pads + t.alpha * t.clearB pads) rest

theorem traceTests_bad (pads : Pad → F) (claim : F) (trace : AssertedTrace Pad Slot F)
    (hbad : AssertedBad pads claim trace) : (traceTests pads claim trace).Bad := by
  induction trace generalizing claim with
  | nil => exact hbad.elim
  | cons entry rest ih =>
      rcases entry with ⟨t, m⟩
      simp only [traceTests, Tests.bad_append, layerTests_bad]
      rcases hbad with hassert | hlayer | hrest
      · exact Or.inl (Or.inl (assertionTests_bad m claim hassert))
      · exact Or.inl (Or.inr hlayer)
      · exact Or.inr (ih _ hrest)

theorem traceTests_valid (pads : Pad → F) (claim : F) (trace : AssertedTrace Pad Slot F) :
    (traceTests pads claim trace).Valid := by
  induction trace generalizing claim with
  | nil => simp [traceTests, Tests.Valid]
  | cons entry rest ih =>
      rcases entry with ⟨t, m⟩
      simp only [traceTests, Tests.valid_append]
      exact ⟨⟨by simp [assertionTests, Tests.Valid, ChallengeTest.Valid],
        layerTests_valid _ _ _ _⟩, ih _⟩

noncomputable def Circuit.tests {out input : ℕ} (circuit : Circuit F out input)
    (messages : circuit.Messages Pad Slot) (w : Cube input → F) (point : Fin out → F)
    (pads : Pad → F) : Tests F :=
  outputTests (circuit.eval w) point ++
    traceTests pads 0 (circuit.execution messages w (monomialWeights point))

theorem Circuit.tests_valid {out input : ℕ} (circuit : Circuit F out input)
    (messages : circuit.Messages Pad Slot) (w : Cube input → F) (point : Fin out → F)
    (pads : Pad → F) : (circuit.tests messages w point pads).Valid := by
  exact (Tests.valid_append _ _).mpr ⟨outputTests_valid _ _, traceTests_valid _ _ _⟩

theorem Circuit.tests_soundness {out input : ℕ} (circuit : Circuit F out input)
    (messages : circuit.Messages Pad Slot) (w : Cube input → F) (point : Fin out → F)
    (pads : Pad → F) (hfalse : ¬ circuit.Satisfies w)
    (haccept : ClearAccepts pads 0 (circuit.proof messages)
      (dot (circuit.inputWeights messages (monomialWeights point)) w)) :
    (circuit.tests messages w point pads).Bad := by
  rcases circuit.soundness_reduction messages w point pads hfalse haccept with houtput | htrace
  · exact (Tests.bad_append _ _).mpr (Or.inl ((outputTests_bad _ _).mpr houtput))
  · exact (Tests.bad_append _ _).mpr (Or.inr (traceTests_bad _ _ _ htrace))

end LfzkV2
