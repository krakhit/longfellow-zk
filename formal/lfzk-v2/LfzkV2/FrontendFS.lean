import LfzkV2.HashReplay
import LfzkV2.BlockOracleSampling

/-!
# The concrete V2 frontend on an adaptive random oracle

The query domain includes arbitrary other protocol roles, so the Polygero
backend can use the same oracle. Their frontend budget is zero. Actual V2
points and their exact tests are supplied by `HashReplay`; no `Covers`
hypothesis or independent-current-challenge assumption is needed.
-/

namespace LfzkV2.Replay

open SumcheckV2 ChallengeBlocks Bcs.TotalOracle Merkle.RandomOracle
open scoped Classical

variable {F C Pad Slot Key Other Out Context Candidate : Type}
variable [Field F] [Fintype F] [DecidableEq F] [Fintype C]
variable {out input N : ℕ}

structure Sampling (F C : Type) [Field F] [Fintype F] [DecidableEq F] [Fintype C]
    {out input : ℕ} (circuit : Circuit F out input) where
  decode : (n : ℕ) → C → Fin n → F
  blocks : ∀ i : Fin (slots circuit), Sampler F C (roleKind circuit ((roleEquiv circuit).symm i))
  agrees : ∀ i, (blocks i).decode = decode (roleKind circuit ((roleEquiv circuit).symm i)).dimension
  unitFiber : ℕ
  balanced : unitFiber * Fintype.card F = Fintype.card C

abbrev Query (Key F : Type) {out input : ℕ} (circuit : Circuit F out input) (Other : Type) :=
  Point Key F circuit ⊕ Other

def queryPoints (circuit : Circuit F out input) : PrefixPoints (Query Key F circuit Other) where
  slot
    | .inl p => (points circuit).slot p
    | .inr _ => 0
  anc p j := match p with
    | .inl p => .inl ((points circuit).anc p j)
    | .inr _ => p
  anc_ne p j hj := by
    cases p with
    | inl p =>
      intro heq
      exact (points circuit).anc_ne p j hj (Sum.inl.inj heq)
    | inr _ =>
      change j < 0 at hj
      omega

def queryKey (circuit : Circuit F out input) (otherKey : Other → Key) : Query Key F circuit Other → Key
  | .inl point => point.1
  | .inr other => otherKey other

def queryKind (circuit : Circuit F out input) : Query Key F circuit Other → Kind
  | .inl point => pointKind circuit point
  | .inr _ => .output 0

noncomputable def emptySampler : Sampler F C (.output 0) where
  decode _ := Fin.elim0
  fiber := Fintype.card C
  fiber_bound _ := Finset.card_le_univ _
  balanced := by simp [Kind.dimension]

noncomputable def querySampler (circuit : Circuit F out input) (sampling : Sampling F C circuit) :
    (query : Query Key F circuit Other) → Sampler F C (queryKind circuit query)
  | .inl (_,none) => emptySampler
  | .inl (_,some p) => sampling.blocks p.1
  | .inr _ => emptySampler

variable [DecidableEq Key] [DecidableEq Other]

variable (circuit : Circuit F out input) (plan : PadPlan (Pad := Pad) (Slot := Slot) circuit)
variable (sampling : Sampling F C circuit) (dflt : C) (otherKey : Other → Key)
variable (adversary : Tree (Query Key F circuit Other) C Out N)
variable (keyOf : Out → Key) (payloadOf : Out → Payload circuit)
variable (context : (Query Key F circuit Other → C) → Key → Context)
variable (context_off : ∀ H H' (x : Query Key F circuit Other), AgreeOff x H H' →
  context H' (queryKey circuit otherKey x) = context H (queryKey circuit otherKey x))
variable (inputValue : Context → Candidate → Cube input → F) (padValue : Context → Candidate → Pad → F)

noncomputable def frontendSetup :
    FiatShamir.BlockOracleSetup F C (Query Key F circuit Other) Out Key Context Candidate N (slots circuit) where
  adversary := adversary
  hashInput out i := .inl (hashInput circuit (keyOf out) (payloadOf out) i)
  points := queryPoints circuit
  key := queryKey circuit otherKey
  context := context
  context_off := context_off
  kind := queryKind circuit
  sampler := querySampler circuit sampling
  unitFiber := sampling.unitFiber
  balanced := sampling.balanced
  test ctx query := match query with
    | .inl point => fun pref candidate => pointData sampling.decode dflt circuit plan point pref
        (inputValue ctx candidate) (padValue ctx candidate)
    | .inr _ => fun _ _ => (fun _ => 0)
  valid ctx query pref candidate := by
    cases query with
    | inl point => exact pointData_valid _ _ _ _ _ _ _ _
    | inr _ => trivial

omit [Field F] [Fintype F] [DecidableEq F] [Fintype C] [DecidableEq Key] [DecidableEq Other] in
theorem queryPrefix_answers (H : Query Key F circuit Other → C) (key : Key)
    (payload : Payload circuit) (i : Fin (slots circuit)) :
    (queryPoints circuit).chal H (.inl (pointAt circuit key payload i)) =
      fun j : Fin i.val => H (.inl (hashInput circuit key payload j.val)) :=
  prefix_answers circuit (fun p => H (.inl p)) key payload i

omit [DecidableEq Key] [DecidableEq Other] in
theorem frontendSetup_hashInput (out : Out) (i : Fin (slots circuit)) :
    (frontendSetup circuit plan sampling dflt otherKey adversary keyOf payloadOf context context_off
      inputValue padValue).hashInput out i.val = .inl (pointAt circuit (keyOf out) (payloadOf out) i) := by
  exact congrArg Sum.inl (hashInput_at circuit (keyOf out) (payloadOf out) i)

omit [DecidableEq Key] [DecidableEq Other] in
theorem frontendSetup_test_at (H : Query Key F circuit Other → C) (ctx : Context) (key : Key)
    (payload : Payload circuit) (i : Fin (slots circuit)) (candidate : Candidate) :
    (frontendSetup circuit plan sampling dflt otherKey adversary keyOf payloadOf context context_off
        inputValue padValue).test ctx (.inl (pointAt circuit key payload i))
          ((queryPoints circuit).chal H (.inl (pointAt circuit key payload i))) candidate =
      semanticData sampling.decode circuit plan payload
        (fun j => H (.inl (hashInput circuit key payload j)))
        (inputValue ctx candidate) (padValue ctx candidate) ((roleEquiv circuit).symm i) := by
  exact pointData_eq sampling.decode dflt circuit plan (fun p => H (.inl p)) key payload i
    (inputValue ctx candidate) (padValue ctx candidate)

/-- The clear frontend verifier recomputes every answer on the shared oracle. -/
noncomputable def oracleAccepts (decode : (n : ℕ) → C → Fin n → F)
    (key : Key) (payload : Payload circuit) (H : Query Key F circuit Other → C)
    (w : Cube input → F) (pads : Pad → F) : Prop :=
  let answers := fun j => H (.inl (hashInput circuit key payload j))
  ClearAccepts pads 0 (circuit.proof (read decode circuit plan payload answers))
    (dot (circuit.inputWeights (read decode circuit plan payload answers)
      (monomialWeights (outputPoint decode out answers))) w)

omit [DecidableEq Key] [DecidableEq Other] in
/-- A false accepting execution yields an actual bad block at an actual
verifier hash point. The test is recovered from that point's prefix. -/
theorem frontendSetup_bad_of_accepts [Fintype Candidate]
    (H : Query Key F circuit Other → C) (candidate : Candidate)
    (hfalse : ¬ circuit.Satisfies
      (inputValue (context H (keyOf (adversary.run H).1)) candidate))
    (haccept : oracleAccepts circuit plan sampling.decode
      (keyOf (adversary.run H).1) (payloadOf (adversary.run H).1) H
      (inputValue (context H (keyOf (adversary.run H).1)) candidate)
      (padValue (context H (keyOf (adversary.run H).1)) candidate)) :
    (frontendSetup circuit plan sampling dflt otherKey adversary keyOf payloadOf context context_off
      inputValue padValue).grinding.RoundBad H := by
  obtain ⟨role,hrole⟩ := semantic_bad_of_accepts sampling.decode circuit plan
    (payloadOf (adversary.run H).1)
    (fun j => H (.inl (hashInput circuit (keyOf (adversary.run H).1)
      (payloadOf (adversary.run H).1) j)))
    (inputValue (context H (keyOf (adversary.run H).1)) candidate)
    (padValue (context H (keyOf (adversary.run H).1)) candidate) hfalse haccept
  obtain ⟨i,rfl⟩ := (roleEquiv circuit).symm.surjective role
  refine ⟨i,candidate,?_⟩
  dsimp only [FiatShamir.BlockOracleSetup.grinding, CtxGrinding.point, CtxGrinding.proof]
  rw [frontendSetup_hashInput]
  change Data.Bad
    ((frontendSetup circuit plan sampling dflt otherKey adversary keyOf payloadOf context context_off
      inputValue padValue).test (context H (keyOf (adversary.run H).1))
        (.inl (pointAt circuit (keyOf (adversary.run H).1) (payloadOf (adversary.run H).1) i))
        ((queryPoints circuit).chal H
          (.inl (pointAt circuit (keyOf (adversary.run H).1) (payloadOf (adversary.run H).1) i))) candidate)
    ((sampling.blocks i).decode
      (H (.inl (pointAt circuit (keyOf (adversary.run H).1) (payloadOf (adversary.run H).1) i))))
  rw [frontendSetup_test_at, sampling.agrees i]
  simp only [Equiv.apply_symm_apply, hashInput_at] at hrole
  convert! hrole using 1

include dflt otherKey context_off

omit [DecidableEq Key] [DecidableEq Other] in
/-- Concrete adaptive FS soundness for the V2 frontend, including proof
selection and arbitrary other roles on the same oracle. Candidate witnesses
and pads may depend on the commitment context fixed off the counted point. -/
theorem frontend_soundness_le [Fintype Key] [Fintype Other] [Fintype Candidate]
    (event : (Query Key F circuit Other → C) → Prop)
    (haccept : ∀ H, event H → ∃ candidate : Candidate,
      ¬ circuit.Satisfies (inputValue (context H (keyOf (adversary.run H).1)) candidate) ∧
      oracleAccepts circuit plan sampling.decode
        (keyOf (adversary.run H).1) (payloadOf (adversary.run H).1) H
        (inputValue (context H (keyOf (adversary.run H).1)) candidate)
        (padValue (context H (keyOf (adversary.run H).1)) candidate)) :
    ((Finset.univ.filter event).card : ℚ) /
        (Fintype.card C : ℚ) ^ Fintype.card (Query Key F circuit Other) ≤
      (Fintype.card Candidate : ℚ) *
        (N * max out 2 + ∑ i : Fin (slots circuit),
          (roleKind circuit ((roleEquiv circuit).symm i)).budget) / Fintype.card F := by
  letI : Nonempty C := ⟨dflt⟩
  refine (frontendSetup circuit plan sampling dflt otherKey adversary keyOf payloadOf context context_off
    inputValue padValue).soundness_le (max out 2) ?_
      (fun i => (roleKind circuit ((roleEquiv circuit).symm i)).budget) ?_ event ?_
  · intro query
    cases query with
    | inl point =>
      rcases point with ⟨key,opt⟩
      cases opt with
      | none => exact Nat.zero_le _
      | some p => exact roleKind_budget_le circuit ((roleEquiv circuit).symm p.1)
    | inr _ => exact Nat.zero_le _
  · intro result i
    rw [frontendSetup_hashInput]
    exact le_refl _
  · intro H hH
    obtain ⟨candidate,hfalse,hcandidate⟩ := haccept H hH
    exact frontendSetup_bad_of_accepts circuit plan sampling dflt otherKey adversary keyOf payloadOf
      context context_off inputValue padValue H candidate hfalse hcandidate

end LfzkV2.Replay
