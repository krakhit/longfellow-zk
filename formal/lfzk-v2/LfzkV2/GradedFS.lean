import LfzkV2.GradedReplay
import Bcs.PotentialChain

/-! V1's graded field/challenge/query accounting for the concrete V2
schedule. Backend weights and residual opening charges are supplied by
Polygero's checked terminal potential. -/

namespace LfzkV2.GradedFS

open Finset SumcheckV2 RecursivePolygero NonrecursiveFS ConcreteFS ChallengeBlocks
  Bcs.TotalOracle Merkle.RandomOracle
open scoped Classical

variable {F C Key Parent Pad Slot Out : Type}
variable [Field F] [Fintype F] [DecidableEq F] [Fintype C]
variable {out input bound N : ℕ}

variable (circuit : Circuit F out input) (I : Instance F)
variable (plan : Replay.PadPlan (Pad := Pad) (Slot := Slot) circuit)
variable (sampling : Replay.Sampling F C circuit) (dflt : C)
variable (keyOf : Parent → Key) (payloadOf : Parent → Replay.Payload circuit)
variable (statement : Reconstruction circuit Pad Slot → I.layer.Statement)
variable (inputValue : I.layer.Oracle → Fin bound → Cube input → F)
variable (padValue : I.layer.Oracle → Fin bound → Pad → F)
variable {cutoff : ℕ} {decodeCoin : C → I.layer.Coin} {decodeQuery : C → I.layer.Query}
variable (P : TerminalPotential I cutoff decodeCoin decodeQuery)

noncomputable def pointBad (W : I.layer.Oracle) (point : Replay.Point Key F circuit)
    (pref : Fin ((Replay.points circuit).slot point) → C) (c : C) : Prop :=
  ∃ candidate : Fin bound,
    Data.Bad (Replay.pointData sampling.decode dflt circuit plan point pref
      (inputValue W candidate) (padValue W candidate))
      ((Replay.querySampler (Other := Unit) circuit sampling (.inl point)).decode c)

theorem pointBad_sum_le (W : I.layer.Oracle) (point : Replay.Point Key F circuit)
    (pref : Fin ((Replay.points circuit).slot point) → C) :
    (∑ c : C, indicator (pointBad circuit I plan sampling dflt inputValue padValue W point pref c)) ≤
      sampling.unitFiber * (bound * (Replay.pointKind circuit point).budget) := by
  rw [show (∑ c : C, indicator (pointBad circuit I plan sampling dflt inputValue padValue W point pref c)) =
      ((univ.filter (pointBad circuit I plan sampling dflt inputValue padValue W point pref)).card : ℚ)
      by simp only [indicator, sum_boole]]
  have hcard : (univ.filter (pointBad circuit I plan sampling dflt inputValue padValue W point pref)).card ≤
      sampling.unitFiber * (bound * (Replay.pointKind circuit point).budget) := by
    have heq : (univ.filter (pointBad circuit I plan sampling dflt inputValue padValue W point pref)) =
        univ.biUnion (fun candidate : Fin bound => univ.filter fun c : C =>
          Data.Bad (Replay.pointData sampling.decode dflt circuit plan point pref
            (inputValue W candidate) (padValue W candidate))
            ((Replay.querySampler (Other := Unit) circuit sampling (.inl point)).decode c)) := by
      ext c
      simp only [mem_filter, mem_univ, true_and, mem_biUnion, pointBad]
    rw [heq]
    calc
      _ ≤ ∑ candidate : Fin bound, (univ.filter fun c : C =>
          Data.Bad (Replay.pointData sampling.decode dflt circuit plan point pref
            (inputValue W candidate) (padValue W candidate))
            ((Replay.querySampler (Other := Unit) circuit sampling (.inl point)).decode c)).card :=
        card_biUnion_le
      _ ≤ ∑ _ : Fin bound, sampling.unitFiber * (Replay.pointKind circuit point).budget :=
        sum_le_sum (fun candidate _ =>
          (Replay.querySampler (Other := Unit) circuit sampling (.inl point)).raw_bad_card
            sampling.unitFiber sampling.balanced _ (Replay.pointData_valid _ _ _ _ _ _ _ _))
      _ = _ := by simp; ring
  exact_mod_cast hcard

def NoSat (I : Instance F) (cutoff : ℕ) (σ : I.layer.Statement) (W : I.layer.Oracle) : Prop :=
  ∀ g ∈ Counting.committedCandidates I W cutoff,
    ¬ I.layer.satisfies σ ((Counting.tupleCounts I).witness g)

noncomputable def charge (W : I.layer.Oracle) (x : Domain Key circuit I Parent)
    (pref : Fin ((GradedReplay.points circuit I keyOf payloadOf).slot x) → C) (c : C) : ℚ :=
  match x with
  | .inl point => indicator (pointBad circuit I plan sampling dflt inputValue padValue W point pref c)
  | .inr (.inl parent) =>
    let σ := statement (GradedReplay.viewAt circuit payloadOf sampling.decode dflt plan parent pref)
    if NoSat I cutoff σ W then P.weight σ W (decodeCoin c) else 0
  | .inr (.inr (parent,response)) =>
    let σ := statement (GradedReplay.viewAt circuit payloadOf sampling.decode dflt plan parent pref)
    let coin := decodeCoin (pref ⟨Replay.slots circuit,
      by change Replay.slots circuit < Replay.slots circuit + 1; omega⟩)
    if NoSat I cutoff σ W ∧ I.layer.verify σ W coin response (decodeQuery c) then
      1-P.weight σ W coin else 0

noncomputable def budget (x : Domain Key circuit I Parent) : ℚ :=
  match x with
  | .inl point => sampling.unitFiber * (bound * (Replay.pointKind circuit point).budget)
  | .inr (.inl _) => P.challengeBudget
  | .inr (.inr _) => P.queryBudget

theorem budget_nonneg (x : Domain Key circuit I Parent) :
    0 ≤ budget (bound := bound) circuit I sampling P x := by
  rcases x with point | parent | pair
  · dsimp only [budget]
    positivity
  · exact P.challengeBudget_nonneg
  · exact P.queryBudget_nonneg

theorem charge_nonneg (W : I.layer.Oracle) (x : Domain Key circuit I Parent)
    (pref : Fin ((GradedReplay.points circuit I keyOf payloadOf).slot x) → C) (c : C) :
    0 ≤ charge circuit I plan sampling dflt keyOf payloadOf statement inputValue padValue
      P W x pref c := by
  rcases x with point | parent | pair
  · exact indicator_nonneg _
  · dsimp only [charge]
    split_ifs
    · exact P.nonneg _ _ _
    · exact le_rfl
  · dsimp only [charge]
    split_ifs
    · exact sub_nonneg.mpr (P.le_one _ _ _)
    · exact le_rfl

theorem charge_sum_le (W : I.layer.Oracle) (x : Domain Key circuit I Parent)
    (pref : Fin ((GradedReplay.points circuit I keyOf payloadOf).slot x) → C) :
    (∑ c : C, charge circuit I plan sampling dflt keyOf payloadOf statement inputValue padValue P W x pref c) ≤
      budget (bound := bound) circuit I sampling P x := by
  rcases x with point | parent | ⟨parent,response⟩
  · exact pointBad_sum_le circuit I plan sampling dflt inputValue padValue W point pref
  · let σ := statement (GradedReplay.viewAt circuit payloadOf sampling.decode dflt plan parent pref)
    change (∑ c : C, if NoSat I cutoff σ W then P.weight σ W (decodeCoin c) else 0) ≤ P.challengeBudget
    by_cases hn : NoSat I cutoff σ W
    · simpa only [if_pos hn] using P.challenge_le σ W
    · simpa only [if_neg hn, sum_const_zero] using P.challengeBudget_nonneg
  · let σ := statement (GradedReplay.viewAt circuit payloadOf sampling.decode dflt plan parent pref)
    let coin := decodeCoin (pref ⟨Replay.slots circuit,
      by change Replay.slots circuit < Replay.slots circuit + 1; omega⟩)
    change (∑ c : C, if NoSat I cutoff σ W ∧ I.layer.verify σ W coin response (decodeQuery c) then
      1-P.weight σ W coin else 0) ≤ P.queryBudget
    by_cases hn : NoSat I cutoff σ W
    · simpa only [hn, true_and] using P.query_le σ W hn coin response
    · simpa only [hn, false_and, if_false, sum_const_zero] using P.queryBudget_nonneg

theorem pointBad_of_frontend_accepts (W : I.layer.Oracle)
    (H : Domain Key circuit I Parent → C) (parent : Parent) (candidate : Fin bound)
    (hfalse : ¬ circuit.Satisfies (inputValue W candidate))
    (haccept : Replay.oracleAccepts circuit plan sampling.decode (keyOf parent) (payloadOf parent) H
      (inputValue W candidate) (padValue W candidate)) :
    ∃ i : Fin (Replay.slots circuit),
      pointBad circuit I plan sampling dflt inputValue padValue W
        (Replay.pointAt circuit (keyOf parent) (payloadOf parent) i)
        ((GradedReplay.points circuit I keyOf payloadOf).chal H
          (.inl (Replay.pointAt circuit (keyOf parent) (payloadOf parent) i)))
        (H (.inl (Replay.pointAt circuit (keyOf parent) (payloadOf parent) i))) := by
  obtain ⟨role,hrole⟩ := Replay.semantic_bad_of_accepts sampling.decode circuit plan (payloadOf parent)
    (fun j => H (.inl (Replay.hashInput circuit (keyOf parent) (payloadOf parent) j)))
    (inputValue W candidate) (padValue W candidate) hfalse haccept
  obtain ⟨i,rfl⟩ := (Replay.roleEquiv circuit).symm.surjective role
  refine ⟨i,candidate,?_⟩
  change Data.Bad (Replay.pointData sampling.decode dflt circuit plan
    (Replay.pointAt circuit (keyOf parent) (payloadOf parent) i)
    ((Replay.points circuit).chal (fun point => H (.inl point))
      (Replay.pointAt circuit (keyOf parent) (payloadOf parent) i))
    (inputValue W candidate) (padValue W candidate))
      ((sampling.blocks i).decode
        (H (.inl (Replay.pointAt circuit (keyOf parent) (payloadOf parent) i))))
  rw [Replay.pointData_eq, sampling.agrees i]
  simp only [Equiv.apply_symm_apply, Replay.hashInput_at] at hrole
  convert! hrole using 1

theorem challenge_charge_eq (W : I.layer.Oracle) (H : Domain Key circuit I Parent → C) (parent : Parent)
    (hnosat : NoSat I cutoff
      (statement (Replay.reconstruction sampling.decode circuit plan (keyOf parent) (payloadOf parent) H)) W) :
    charge circuit I plan sampling dflt keyOf payloadOf statement inputValue padValue P W
      (ConcreteFS.parent circuit I parent)
      ((GradedReplay.points circuit I keyOf payloadOf).chal H (ConcreteFS.parent circuit I parent))
      (H (ConcreteFS.parent circuit I parent)) =
        P.weight (statement (Replay.reconstruction sampling.decode circuit plan
          (keyOf parent) (payloadOf parent) H)) W (decodeCoin (H (ConcreteFS.parent circuit I parent))) := by
  let v := GradedReplay.viewAt circuit payloadOf sampling.decode dflt plan parent
    ((GradedReplay.points circuit I keyOf payloadOf).chal H (ConcreteFS.parent circuit I parent))
  change (if NoSat I cutoff (statement v) W then
    P.weight (statement v) W (decodeCoin (H (ConcreteFS.parent circuit I parent))) else 0) = _
  rw [show v = Replay.reconstruction sampling.decode circuit plan (keyOf parent) (payloadOf parent) H from
    GradedReplay.parent_view_eq circuit I keyOf payloadOf sampling.decode dflt plan H parent,
    if_pos hnosat]

theorem query_charge_eq (W : I.layer.Oracle) (H : Domain Key circuit I Parent → C)
    (parent : Parent) (response : I.layer.Payload)
    (hnosat : NoSat I cutoff
      (statement (Replay.reconstruction sampling.decode circuit plan (keyOf parent) (payloadOf parent) H)) W)
    (haccept : I.layer.verify
      (statement (Replay.reconstruction sampling.decode circuit plan (keyOf parent) (payloadOf parent) H)) W
      (decodeCoin (H (ConcreteFS.parent circuit I parent))) response
      (decodeQuery (H (ConcreteFS.child circuit I parent response)))) :
    charge circuit I plan sampling dflt keyOf payloadOf statement inputValue padValue P W
      (ConcreteFS.child circuit I parent response)
      ((GradedReplay.points circuit I keyOf payloadOf).chal H (ConcreteFS.child circuit I parent response))
      (H (ConcreteFS.child circuit I parent response)) =
        1-P.weight (statement (Replay.reconstruction sampling.decode circuit plan
          (keyOf parent) (payloadOf parent) H)) W (decodeCoin (H (ConcreteFS.parent circuit I parent))) := by
  let v := GradedReplay.viewAt circuit payloadOf sampling.decode dflt plan parent
    ((GradedReplay.points circuit I keyOf payloadOf).chal H (ConcreteFS.child circuit I parent response))
  let coin := decodeCoin ((GradedReplay.points circuit I keyOf payloadOf).chal H
    (ConcreteFS.child circuit I parent response)
      ⟨Replay.slots circuit,by change Replay.slots circuit < Replay.slots circuit+1; omega⟩)
  change (if NoSat I cutoff (statement v) W ∧ I.layer.verify (statement v) W coin response
    (decodeQuery (H (ConcreteFS.child circuit I parent response))) then 1-P.weight (statement v) W coin else 0) = _
  rw [show v = Replay.reconstruction sampling.decode circuit plan (keyOf parent) (payloadOf parent) H from
    GradedReplay.child_view_eq circuit I keyOf payloadOf sampling.decode dflt plan H parent response,
    show coin = decodeCoin (H (ConcreteFS.parent circuit I parent)) from
      congrArg decodeCoin (GradedReplay.child_coin_eq circuit I keyOf payloadOf H parent response),
    if_pos ⟨hnosat,haccept⟩]

noncomputable def maxBudget : ℚ :=
  max ((sampling.unitFiber : ℚ) * (bound * max out 2)) (max P.challengeBudget P.queryBudget)

theorem maxBudget_nonneg : 0 ≤ maxBudget (bound := bound) circuit I sampling P := by
  unfold maxBudget
  apply le_trans _ (le_max_left _ _)
  positivity

theorem budget_le_max (x : Domain Key circuit I Parent) :
    budget (bound := bound) circuit I sampling P x ≤ maxBudget (bound := bound) circuit I sampling P := by
  unfold budget maxBudget
  rcases x with ⟨key,opt⟩ | parent | pair
  · cases opt with
    | none =>
      change (sampling.unitFiber : ℚ) * (bound * 0) ≤ _
      simpa only [maxBudget, mul_zero] using maxBudget_nonneg (bound := bound) circuit I sampling P
    | some p =>
      apply le_trans _ (le_max_left _ _)
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          ((Nat.cast_le (α := ℚ)).mpr (Replay.roleKind_budget_le circuit ((Replay.roleEquiv circuit).symm p.1)))
          (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  · exact (le_max_left P.challengeBudget P.queryBudget).trans (le_max_right _ _)
  · exact (le_max_right P.challengeBudget P.queryBudget).trans (le_max_right _ _)

noncomputable def slotBudget (i : Fin (Replay.slots circuit + 2)) : ℚ :=
  if h : i.val < Replay.slots circuit then
    sampling.unitFiber * (bound * (Replay.roleKind circuit ((Replay.roleEquiv circuit).symm ⟨i.val,h⟩)).budget)
  else if i.val = Replay.slots circuit then P.challengeBudget else P.queryBudget

theorem budget_hashInput (selected : Parent × I.layer.Payload) (i : Fin (Replay.slots circuit + 2)) :
    budget (bound := bound) circuit I sampling P (GradedReplay.hashInput circuit I keyOf payloadOf selected i.val) =
      slotBudget (bound := bound) circuit I sampling P i := by
  unfold GradedReplay.hashInput slotBudget
  split_ifs with hfield
  · rw [Replay.hashInput_at circuit _ _ ⟨i.val,hfield⟩]
    rfl
  · rfl
  · rfl

/-- The same one-slot-or-terminal-pair split as V1. If no frontend root
event occurs, every member of the committed list fails the built system,
and the two actual backend roles pay a total of one. -/
theorem path_charge_ge_one (W : I.layer.Oracle) (H : Domain Key circuit I Parent → C)
    (selected : Parent × I.layer.Payload)
    (hcard : (Counting.committedCandidates I W cutoff).card ≤ bound)
    (hfalse : ∀ candidate : Fin bound,
      Counting.committedCandidate I W cutoff bound candidate ∈ Counting.committedCandidates I W cutoff →
      ¬ circuit.Satisfies (inputValue W candidate))
    (hfront : ∀ candidate : Fin bound,
      I.layer.satisfies
        (statement (Replay.reconstruction sampling.decode circuit plan
          (keyOf selected.1) (payloadOf selected.1) H))
        ((Counting.tupleCounts I).witness (Counting.committedCandidate I W cutoff bound candidate)) →
      Replay.oracleAccepts circuit plan sampling.decode (keyOf selected.1) (payloadOf selected.1) H
        (inputValue W candidate) (padValue W candidate))
    (haccept : I.layer.verify
      (statement (Replay.reconstruction sampling.decode circuit plan
        (keyOf selected.1) (payloadOf selected.1) H)) W
      (decodeCoin (H (ConcreteFS.parent circuit I selected.1))) selected.2
      (decodeQuery (H (ConcreteFS.child circuit I selected.1 selected.2)))) :
    1 ≤ ∑ i : Fin (Replay.slots circuit + 2),
      charge circuit I plan sampling dflt keyOf payloadOf statement inputValue padValue P W
        (GradedReplay.hashInput circuit I keyOf payloadOf selected i.val)
        ((GradedReplay.points circuit I keyOf payloadOf).chal H
          (GradedReplay.hashInput circuit I keyOf payloadOf selected i.val))
        (H (GradedReplay.hashInput circuit I keyOf payloadOf selected i.val)) := by
  apply Bcs.PotentialChain.one_or_two_slots_pay _
    (fun i => charge_nonneg circuit I plan sampling dflt keyOf payloadOf statement inputValue padValue P W _ _ _)
  by_cases hb : ∃ i : Fin (Replay.slots circuit),
      pointBad circuit I plan sampling dflt inputValue padValue W
        (Replay.pointAt circuit (keyOf selected.1) (payloadOf selected.1) i)
        ((GradedReplay.points circuit I keyOf payloadOf).chal H
          (.inl (Replay.pointAt circuit (keyOf selected.1) (payloadOf selected.1) i)))
        (H (.inl (Replay.pointAt circuit (keyOf selected.1) (payloadOf selected.1) i)))
  · obtain ⟨i,hi⟩ := hb
    left
    refine ⟨⟨i.val,by omega⟩,?_⟩
    rw [GradedReplay.hashInput, if_pos i.isLt, Replay.hashInput_at circuit _ _ i]
    change 1 ≤ indicator (pointBad circuit I plan sampling dflt inputValue padValue W _ _ _)
    simp only [indicator, if_pos hi, le_refl]
  · have hn : NoSat I cutoff
        (statement (Replay.reconstruction sampling.decode circuit plan
          (keyOf selected.1) (payloadOf selected.1) H)) W := by
      intro g hg hsat
      obtain ⟨candidate,hcandidate⟩ := Counting.exists_committedCandidate I W cutoff bound hcard g hg
      rw [← hcandidate] at hsat
      exact hb (pointBad_of_frontend_accepts circuit I plan sampling dflt keyOf payloadOf
        inputValue padValue W H selected.1 candidate
        (hfalse candidate (by rw [hcandidate]; exact hg)) (hfront candidate hsat))
    right
    refine ⟨⟨Replay.slots circuit,by omega⟩,⟨Replay.slots circuit+1,by omega⟩,?_,?_⟩
    · intro heq
      have h := congrArg Fin.val heq
      change Replay.slots circuit = Replay.slots circuit+1 at h
      omega
    · have hchallenge : GradedReplay.hashInput circuit I keyOf payloadOf selected (Replay.slots circuit) =
          ConcreteFS.parent circuit I selected.1 := by
        rw [GradedReplay.hashInput, if_neg (Nat.lt_irrefl _), if_pos rfl]
      have hquery : GradedReplay.hashInput circuit I keyOf payloadOf selected (Replay.slots circuit+1) =
          ConcreteFS.child circuit I selected.1 selected.2 := by
        rw [GradedReplay.hashInput, if_neg (by omega), if_neg (by omega)]
      dsimp only [Fin.val_mk]
      rw [hchallenge,hquery,
        challenge_charge_eq circuit I plan sampling dflt keyOf payloadOf statement inputValue padValue P W H selected.1 hn,
        query_charge_eq circuit I plan sampling dflt keyOf payloadOf statement inputValue padValue P W H selected.1 selected.2 hn haccept]
      linarith

variable [DecidableEq Key] [DecidableEq Parent]

def grinding (tree : Tree (Domain Key circuit I Parent) C Out N)
    (selected : Out → Parent × I.layer.Payload)
    (context : (Domain Key circuit I Parent → C) → Key → I.layer.Oracle)
    (context_off : ∀ H H' x, AgreeOff x H H' →
      context H' (Replay.queryKey circuit (roleKey I keyOf) x) =
        context H (Replay.queryKey circuit (roleKey I keyOf) x)) :
    CtxGrinding C (Domain Key circuit I Parent) Out Key I.layer.Oracle N (Replay.slots circuit + 2) where
  adversary := tree
  hashInput result := GradedReplay.hashInput circuit I keyOf payloadOf (selected result)
  pts := GradedReplay.points circuit I keyOf payloadOf
  key := Replay.queryKey circuit (roleKey I keyOf)
  ctxAt := context
  ctxAt_off := context_off
  Bad _ _ _ _ := False
  beta _ := 0
  bad_bound := by intros; simp

include dflt

omit [DecidableEq Key] [DecidableEq Parent] in
/-- V1's rational potential compiler on the actual V2 schedule. The only
frontend transfer premise is algebraic satisfaction of the built backend
statement; it is instantiated by the concrete compiler below. -/
theorem event_soundness_le [Fintype Key] [Fintype Parent]
    (tree : Tree (Domain Key circuit I Parent) C Out N)
    (selected : Out → Parent × I.layer.Payload)
    (context : (Domain Key circuit I Parent → C) → Key → I.layer.Oracle)
    (context_off : ∀ H H' x, AgreeOff x H H' →
      context H' (Replay.queryKey circuit (roleKey I keyOf) x) =
        context H (Replay.queryKey circuit (roleKey I keyOf) x))
    (hcard : ∀ W, (Counting.committedCandidates I W cutoff).card ≤ bound)
    (event : (Domain Key circuit I Parent → C) → Prop) [DecidablePred event]
    (hfalse : ∀ H, event H → ∀ candidate : Fin bound,
      Counting.committedCandidate I (context H (keyOf (selected (tree.run H).1).1)) cutoff bound candidate ∈
        Counting.committedCandidates I (context H (keyOf (selected (tree.run H).1).1)) cutoff →
      ¬ circuit.Satisfies (inputValue (context H (keyOf (selected (tree.run H).1).1)) candidate))
    (hfront : ∀ (H : Domain Key circuit I Parent → C) (parent : Parent) (candidate : Fin bound),
      I.layer.satisfies
        (statement (Replay.reconstruction sampling.decode circuit plan (keyOf parent) (payloadOf parent) H))
        ((Counting.tupleCounts I).witness
          (Counting.committedCandidate I (context H (keyOf parent)) cutoff bound candidate)) →
      Replay.oracleAccepts circuit plan sampling.decode (keyOf parent) (payloadOf parent) H
        (inputValue (context H (keyOf parent)) candidate) (padValue (context H (keyOf parent)) candidate))
    (haccept : ∀ H, event H →
      let i := selected (tree.run H).1
      I.layer.verify
        (statement (Replay.reconstruction sampling.decode circuit plan (keyOf i.1) (payloadOf i.1) H))
        (context H (keyOf i.1)) (decodeCoin (H (ConcreteFS.parent circuit I i.1))) i.2
        (decodeQuery (H (ConcreteFS.child circuit I i.1 i.2)))) :
    ((univ.filter event).card : ℚ)/(Fintype.card C : ℚ)^Fintype.card (Domain Key circuit I Parent) ≤
      (N * maxBudget (bound := bound) circuit I sampling P +
        ∑ i : Fin (Replay.slots circuit+2), slotBudget (bound := bound) circuit I sampling P i)/Fintype.card C := by
  letI : Nonempty C := ⟨dflt⟩
  let G := grinding circuit I keyOf payloadOf tree selected context context_off
  refine G.potential_ratio_le_rat
    (charge circuit I plan sampling dflt keyOf payloadOf statement inputValue padValue P)
    (charge_nonneg circuit I plan sampling dflt keyOf payloadOf statement inputValue padValue P)
    (budget (bound := bound) circuit I sampling P) (budget_nonneg (bound := bound) circuit I sampling P)
    (charge_sum_le circuit I plan sampling dflt keyOf payloadOf statement inputValue padValue P)
    (maxBudget (bound := bound) circuit I sampling P) (maxBudget_nonneg (bound := bound) circuit I sampling P)
    (budget_le_max (bound := bound) circuit I sampling P)
    (slotBudget (bound := bound) circuit I sampling P)
    (fun result i => (budget_hashInput (bound := bound) circuit I sampling keyOf payloadOf P (selected result) i).le)
    event ?_
  intro H hevent
  let s := selected (tree.run H).1
  let W := context H (keyOf s.1)
  have hp := path_charge_ge_one circuit I plan sampling dflt keyOf payloadOf statement inputValue padValue P
    W H s (hcard W) (hfalse H hevent) (hfront H s.1) (haccept H hevent)
  let f := fun x : Domain Key circuit I Parent =>
    charge circuit I plan sampling dflt keyOf payloadOf statement inputValue padValue P
      (context H (G.key x)) x (G.pts.chal H x) (H x)
  apply le_trans _ (G.verifier_charge_le_total
    (fun result => GradedReplay.hashInput_injective circuit I keyOf payloadOf (selected result)) f
    (fun x => charge_nonneg circuit I plan sampling dflt keyOf payloadOf statement inputValue padValue P
      (context H (G.key x)) x (G.pts.chal H x) (H x)) H)
  refine hp.trans_eq ?_
  apply sum_congr rfl
  intro i _
  dsimp only [f]
  have hk : G.key (G.point H i.val) = keyOf s.1 :=
    GradedReplay.hashInput_key circuit I keyOf payloadOf s i.val
  rw [hk]
  rfl

omit [DecidableEq Key] [DecidableEq Parent] in
theorem soundness_le [Fintype Key] [Fintype Parent]
    (tree : Tree (Domain Key circuit I Parent) C Out N)
    (selected : Out → Parent × I.layer.Payload)
    (context : (Domain Key circuit I Parent → C) → Key → I.layer.Oracle)
    (context_off : ∀ H H' x, AgreeOff x H H' →
      context H' (Replay.queryKey circuit (roleKey I keyOf) x) =
        context H (Replay.queryKey circuit (roleKey I keyOf) x))
    (hcard : ∀ W, (Counting.committedCandidates I W cutoff).card ≤ bound)
    (hfalse : ∀ W candidate, ¬ circuit.Satisfies (inputValue W candidate))
    (hfront : ∀ (H : Domain Key circuit I Parent → C) (parent : Parent) (candidate : Fin bound),
      I.layer.satisfies
        (statement (Replay.reconstruction sampling.decode circuit plan (keyOf parent) (payloadOf parent) H))
        ((Counting.tupleCounts I).witness
          (Counting.committedCandidate I (context H (keyOf parent)) cutoff bound candidate)) →
      Replay.oracleAccepts circuit plan sampling.decode (keyOf parent) (payloadOf parent) H
        (inputValue (context H (keyOf parent)) candidate) (padValue (context H (keyOf parent)) candidate)) :
    let accepts := fun H : Domain Key circuit I Parent → C =>
      let i := selected (tree.run H).1
      I.layer.verify
        (statement (Replay.reconstruction sampling.decode circuit plan (keyOf i.1) (payloadOf i.1) H))
        (context H (keyOf i.1)) (decodeCoin (H (ConcreteFS.parent circuit I i.1))) i.2
        (decodeQuery (H (ConcreteFS.child circuit I i.1 i.2)))
    ((univ.filter accepts).card : ℚ)/(Fintype.card C : ℚ)^Fintype.card (Domain Key circuit I Parent) ≤
      (N * maxBudget (bound := bound) circuit I sampling P +
        ∑ i : Fin (Replay.slots circuit+2), slotBudget (bound := bound) circuit I sampling P i)/Fintype.card C := by
  intro accepts
  exact event_soundness_le circuit I plan sampling dflt keyOf payloadOf statement inputValue padValue P
    tree selected context context_off hcard accepts (fun _ _ _ _ => hfalse _ _) hfront (fun _ h => h)

omit [DecidableEq Key] [DecidableEq Parent] in
/-- The concrete compiled V2 verifier with graded Polygero terminal charges.
The fixed-list frontend transfer and its false-statement premise follow
from the actual affine rows, product checks, and public/private input split. -/
theorem compiled_soundness_le [Fintype Key] [Fintype Parent]
    {nPublic nPrivate : ℕ}
    (index : (Fin nPublic ⊕ Fin nPrivate) ↪ Cube input)
    (publicInputs : Fin nPublic → F) (privateCoordinate : Fin nPrivate → Slot)
    (coordinate : Pad → Slot)
    (primary : Slot → Fin I.nw × Fin I.q)
    (product : (v : Reconstruction circuit Pad Slot) →
      Fin v.constraints.layers.length → Fin I.nq × Fin I.q)
    (eqns : (v : Reconstruction circuit Pad Slot) → I.Equations ≃ Backend.Equation
      (v.rows index publicInputs privateCoordinate coordinate).length v.constraints.layers.length)
    (hcutoff : I.r+I.w-1 < cutoff)
    (hpacking : CodingTheory.UniformFamilyBound I.n cutoff (I.r+I.w-1) bound)
    (tree : Tree (Domain Key circuit I Parent) C Out N)
    (selected : Out → Parent × I.layer.Payload)
    (context : (Domain Key circuit I Parent → C) → Key → I.layer.Oracle)
    (context_off : ∀ H H' x, AgreeOff x H H' →
      context H' (Replay.queryKey circuit (roleKey I keyOf) x) =
        context H (Replay.queryKey circuit (roleKey I keyOf) x))
    (hfalse : ∀ privateInputs : Fin nPrivate → F,
      ¬ circuit.Satisfies (zeroExtend index (Sum.elim publicInputs privateInputs))) :
    let accepts := fun H : Domain Key circuit I Parent → C =>
      let i := selected (tree.run H).1
      let v := Replay.reconstruction sampling.decode circuit plan (keyOf i.1) (payloadOf i.1) H
      I.layer.verify (v.backendStatement index publicInputs privateCoordinate coordinate
        I primary (product v) (eqns v)) (context H (keyOf i.1))
        (decodeCoin (H (ConcreteFS.parent circuit I i.1))) i.2
        (decodeQuery (H (ConcreteFS.child circuit I i.1 i.2)))
    ((univ.filter accepts).card : ℚ)/(Fintype.card C : ℚ)^Fintype.card (Domain Key circuit I Parent) ≤
      (N * maxBudget (bound := bound) circuit I sampling P +
        ∑ i : Fin (Replay.slots circuit+2), slotBudget (bound := bound) circuit I sampling P i)/Fintype.card C := by
  let statement := fun v : Reconstruction circuit Pad Slot =>
    v.backendStatement index publicInputs privateCoordinate coordinate I primary (product v) (eqns v)
  let values := fun W candidate => Backend.read ((Counting.tupleCounts I).witness
    (Counting.committedCandidate I W cutoff bound candidate)) ∘ Backend.linearAddress primary
  apply soundness_le circuit I plan sampling dflt keyOf payloadOf statement
    (fun W candidate => circuitInputs index publicInputs privateCoordinate (values W candidate))
    (fun W candidate => values W candidate ∘ coordinate) P tree selected context context_off
    (fun W => Counting.committedCandidates_card_le I W cutoff bound hcutoff hpacking)
    (fun _ _ => hfalse _)
  intro H parent candidate hsat
  apply Replay.reconstruction_accepts sampling.decode circuit plan (keyOf parent) (payloadOf parent)
    H index publicInputs privateCoordinate coordinate (values (context H (keyOf parent)) candidate)
  exact (Replay.reconstruction sampling.decode circuit plan (keyOf parent) (payloadOf parent) H).satisfies_accepts
    index publicInputs privateCoordinate coordinate I primary _ _ _ hsat

omit [DecidableEq Key] [DecidableEq Parent] in
/-- Extraction-first form, as used in V1's two-field MAC composition.
Acceptance without a satisfying member of the actual committed list pays
the same graded budget, even when the public side statement is satisfiable. -/
theorem compiled_extraction_failure_le [Fintype Key] [Fintype Parent]
    {nPublic nPrivate : ℕ}
    (index : (Fin nPublic ⊕ Fin nPrivate) ↪ Cube input)
    (publicInputs : Fin nPublic → F) (privateCoordinate : Fin nPrivate → Slot)
    (coordinate : Pad → Slot)
    (primary : Slot → Fin I.nw × Fin I.q)
    (product : (v : Reconstruction circuit Pad Slot) →
      Fin v.constraints.layers.length → Fin I.nq × Fin I.q)
    (eqns : (v : Reconstruction circuit Pad Slot) → I.Equations ≃ Backend.Equation
      (v.rows index publicInputs privateCoordinate coordinate).length v.constraints.layers.length)
    (hcutoff : I.r+I.w-1 < cutoff)
    (hpacking : CodingTheory.UniformFamilyBound I.n cutoff (I.r+I.w-1) bound)
    (tree : Tree (Domain Key circuit I Parent) C Out N)
    (selected : Out → Parent × I.layer.Payload)
    (context : (Domain Key circuit I Parent → C) → Key → I.layer.Oracle)
    (context_off : ∀ H H' x, AgreeOff x H H' →
      context H' (Replay.queryKey circuit (roleKey I keyOf) x) =
        context H (Replay.queryKey circuit (roleKey I keyOf) x)) :
    let fails := fun H : Domain Key circuit I Parent → C =>
      let i := selected (tree.run H).1
      let W := context H (keyOf i.1)
      let v := Replay.reconstruction sampling.decode circuit plan (keyOf i.1) (payloadOf i.1) H
      I.layer.verify (v.backendStatement index publicInputs privateCoordinate coordinate
        I primary (product v) (eqns v)) W
        (decodeCoin (H (ConcreteFS.parent circuit I i.1))) i.2
        (decodeQuery (H (ConcreteFS.child circuit I i.1 i.2))) ∧
      ¬ ∃ g ∈ Counting.committedCandidates I W cutoff,
        circuit.Satisfies (circuitInputs index publicInputs privateCoordinate
          (Backend.read ((Counting.tupleCounts I).witness g) ∘ Backend.linearAddress primary))
    ((univ.filter fails).card : ℚ)/(Fintype.card C : ℚ)^Fintype.card (Domain Key circuit I Parent) ≤
      (N * maxBudget (bound := bound) circuit I sampling P +
        ∑ i : Fin (Replay.slots circuit+2), slotBudget (bound := bound) circuit I sampling P i)/Fintype.card C := by
  intro fails
  let statement := fun v : Reconstruction circuit Pad Slot =>
    v.backendStatement index publicInputs privateCoordinate coordinate I primary (product v) (eqns v)
  let values := fun W candidate => Backend.read ((Counting.tupleCounts I).witness
    (Counting.committedCandidate I W cutoff bound candidate)) ∘ Backend.linearAddress primary
  apply event_soundness_le circuit I plan sampling dflt keyOf payloadOf statement
    (fun W candidate => circuitInputs index publicInputs privateCoordinate (values W candidate))
    (fun W candidate => values W candidate ∘ coordinate) P tree selected context context_off
    (fun W => Counting.committedCandidates_card_le I W cutoff bound hcutoff hpacking) fails
  · intro H hH candidate hmem hsat
    exact hH.2 ⟨_,hmem,hsat⟩
  · intro H parent candidate hsat
    apply Replay.reconstruction_accepts sampling.decode circuit plan (keyOf parent) (payloadOf parent)
      H index publicInputs privateCoordinate coordinate (values (context H (keyOf parent)) candidate)
    exact (Replay.reconstruction sampling.decode circuit plan (keyOf parent) (payloadOf parent) H).satisfies_accepts
      index publicInputs privateCoordinate coordinate I primary _ _ _ hsat
  · intro H hH
    exact hH.1

end LfzkV2.GradedFS
