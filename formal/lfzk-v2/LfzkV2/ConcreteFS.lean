import LfzkV2.CompiledReplay
import polygero.FiatShamir.CommittedComposition

/-!
# Concrete V2 frontend and Polygero on one adaptive oracle

The frontend points carry their actual message prefixes. The two backend
roles carry the complete frontend payload and, for the query, the complete
response. Replaying this transcript constructs the compiled statement.
The committed oracle context is fixed off each point naming its key;
the two-coordinate condition used by Polygero follows from that premise.
-/

namespace LfzkV2.ConcreteFS

open SumcheckV2 RecursivePolygero Counting Finset Bcs.TotalOracle Merkle.RandomOracle
open scoped Classical

variable {F C Key Parent Out Pad Slot : Type}
variable [Field F] [Fintype F] [DecidableEq F]
variable {out input N nPublic nPrivate : ℕ}

abbrev BackendRoles (I : Instance F) (Parent : Type) := Parent ⊕ (Parent × I.layer.Payload)

abbrev Domain (Key : Type) (circuit : Circuit F out input) (I : Instance F) (Parent : Type) :=
  Replay.Query Key F circuit (BackendRoles I Parent)

def parent (circuit : Circuit F out input) (I : Instance F) (j : Parent) : Domain Key circuit I Parent :=
  .inr (.inl j)

def child (circuit : Circuit F out input) (I : Instance F) (j : Parent) (response : I.layer.Payload) :
    Domain Key circuit I Parent := .inr (.inr (j,response))

def roleKey (I : Instance F) (keyOf : Parent → Key) : BackendRoles I Parent → Key
  | .inl j => keyOf j
  | .inr (j,_) => keyOf j

variable [Fintype C] [Fintype Key] [Fintype Parent]

/-- Soundness of the actual replayed V2 compiler and Polygero decoder in the
ideal-binding model. Every frontend replay and root-counting obligation is
discharged; the remaining context premise is the commitment interface. -/
theorem soundness_le
    (circuit : Circuit F out input) (plan : Replay.PadPlan (Pad := Pad) (Slot := Slot) circuit)
    (sampling : Replay.Sampling F C circuit) (dflt : C)
    (index : (Fin nPublic ⊕ Fin nPrivate) ↪ Cube input)
    (publicInputs : Fin nPublic → F) (privateCoordinate : Fin nPrivate → Slot)
    (coordinate : Pad → Slot)
    (I : Instance F) (parameters : HahnSystemCertificate I)
    (hsmall : parameters.rankError ≤ 1/(Nat.card F : ℚ))
    (cutoff bound : ℕ) (hcutoff : I.r+I.w-1 < cutoff)
    (hpacking : CodingTheory.UniformFamilyBound I.n cutoff (I.r+I.w-1) bound)
    (tree : Tree (Domain Key circuit I Parent) C Out N)
    (selected : Out → Parent × I.layer.Payload)
    (keyOf : Parent → Key) (payloadOf : Parent → Replay.Payload circuit)
    (context : (Domain Key circuit I Parent → C) → Key → I.layer.Oracle)
    (context_off : ∀ H H' x, AgreeOff x H H' →
      context H' (Replay.queryKey circuit (roleKey I keyOf) x) =
        context H (Replay.queryKey circuit (roleKey I keyOf) x))
    (primary : Slot → Fin I.nw × Fin I.q)
    (product : (v : Reconstruction circuit Pad Slot) →
      Fin v.constraints.layers.length → Fin I.nq × Fin I.q)
    (eqns : (v : Reconstruction circuit Pad Slot) → I.Equations ≃ Backend.Equation
      (v.rows index publicInputs privateCoordinate coordinate).length v.constraints.layers.length)
    [DecidableEq I.layer.Coin] [DecidableEq I.layer.Query]
    (decodeCoin : C → I.layer.Coin) (decodeQuery : C → I.layer.Query)
    (kCoin kQuery : ℕ)
    (hcoin : ∀ coin, (univ.filter fun a : C => decodeCoin a = coin).card ≤ kCoin)
    (hquery : ∀ query, (univ.filter fun b : C => decodeQuery b = query).card ≤ kQuery)
    (hkCoin : kCoin*Fintype.card I.layer.Coin ≤ Fintype.card C)
    (hkQuery : kQuery*Fintype.card I.layer.Query ≤ Fintype.card C)
    (hfalse : ∀ privateInputs : Fin nPrivate → F,
      ¬ circuit.Satisfies (zeroExtend index (Sum.elim publicInputs privateInputs))) :
    let accepts := fun H : Domain Key circuit I Parent → C =>
      let i := selected (tree.run H).1
      let v := Replay.reconstruction sampling.decode circuit plan (keyOf i.1) (payloadOf i.1) H
      I.layer.verify (v.backendStatement index publicInputs privateCoordinate coordinate
        I primary (product v) (eqns v)) (context H (keyOf i.1))
          (decodeCoin (H (parent circuit I i.1))) i.2 (decodeQuery (H (child circuit I i.1 i.2)))
    ((univ.filter accepts).card : ℚ)/(Fintype.card C : ℚ)^Fintype.card (Domain Key circuit I Parent) ≤
      (N+1 : ℕ)*(parameters.error + ((cutoff+I.s-1).choose I.t : ℚ)/I.n.choose I.t) +
        (bound : ℚ)*(N*max out 2 + ∑ i : Fin (Replay.slots circuit),
          (Replay.roleKind circuit ((Replay.roleEquiv circuit).symm i)).budget)/Fintype.card F := by
  letI : Nonempty C := ⟨dflt⟩
  intro accepts
  let chosen := fun H : Domain Key circuit I Parent → C => selected (tree.run H).1
  let view := fun j (H : Domain Key circuit I Parent → C) =>
    Replay.reconstruction sampling.decode circuit plan (keyOf j) (payloadOf j) H
  let state := fun j H => (view j H,context H (keyOf j))
  let statement := fun v : Reconstruction circuit Pad Slot =>
    v.backendStatement index publicInputs privateCoordinate coordinate I primary (product v) (eqns v)
  let values := fun ctx candidate => Backend.read ((tupleCounts I).witness
    (committedCandidate I ctx cutoff bound candidate)) ∘ Backend.linearAddress primary
  let frontend := fun H : Domain Key circuit I Parent → C => ∃ candidate : Fin bound,
    (view (chosen H).1 H).Accepts index publicInputs privateCoordinate coordinate
      (values (context H (keyOf (chosen H).1)) candidate)
  letI : DecidablePred frontend := fun _ => Classical.propDecidable _
  have hstateOff j response H H'
      (hoff : ∀ z, z ≠ parent circuit I j → z ≠ child circuit I j response → H z = H' z) :
      state j H = state j H' := by
    refine Prod.ext ?_ ?_
    · apply Replay.reconstruction_eq_of_answers
      intro k
      exact hoff _ (by intro he; cases he) (by intro he; cases he)
    · exact Replay.context_eq_of_off_two context (Replay.queryKey circuit (roleKey I keyOf))
        context_off (parent circuit I j) (child circuit I j response) rfl H H' hoff
  have hfront : ((univ.filter frontend).card : ℚ)/
      (Fintype.card C : ℚ)^Fintype.card (Domain Key circuit I Parent) ≤
        (bound : ℚ)*(N*max out 2 + ∑ i : Fin (Replay.slots circuit),
          (Replay.roleKind circuit ((Replay.roleEquiv circuit).symm i)).budget)/Fintype.card F := by
    have h := Replay.frontend_soundness_le circuit plan sampling dflt (roleKey I keyOf) tree
      (fun result => keyOf (selected result).1) (fun result => payloadOf (selected result).1)
      context context_off
      (fun ctx candidate => circuitInputs index publicInputs privateCoordinate (values ctx candidate))
      (fun ctx candidate => values ctx candidate ∘ coordinate) frontend (by
        intro H hH
        obtain ⟨candidate,hcandidate⟩ := hH
        refine ⟨candidate,hfalse _,?_⟩
        exact Replay.reconstruction_accepts sampling.decode circuit plan
          (keyOf (chosen H).1) (payloadOf (chosen H).1) H index publicInputs privateCoordinate
          coordinate _ hcandidate)
    simpa only [Fintype.card_fin] using h
  convert! NonrecursiveFS.committed_composition_le I parameters hsmall tree selected
    (parent circuit I) (child circuit I)
    (by intro a b h; exact Sum.inl.inj (Sum.inr.inj h))
    (by intro a b h; exact Sum.inr.inj (Sum.inr.inj h))
    (by intro j j' response; simp [parent, child])
    state hstateOff (fun s _ => statement s.1) (fun s _ => s.2)
    decodeCoin decodeQuery kCoin kQuery hcoin hquery hkCoin hkQuery cutoff bound hcutoff hpacking
    (fun H g => (view (chosen H).1 H).Accepts index publicInputs privateCoordinate coordinate
      (Backend.read ((tupleCounts I).witness g) ∘ Backend.linearAddress primary))
    (by
      intro H g
      dsimp only
      intro hdecode
      exact (view (chosen H).1 H).decoded_accepts index publicInputs privateCoordinate coordinate
        I primary (product (view (chosen H).1 H)) (eqns (view (chosen H).1 H))
        (context H (keyOf (chosen H).1)) (decodeCoin (H (parent circuit I (chosen H).1)))
        (chosen H).2 g hdecode)
    _ (by
      convert! hfront using 1
      congr 3
      ext H
      simp only [mem_filter, frontend, values, chosen, state]) using 1

end LfzkV2.ConcreteFS
