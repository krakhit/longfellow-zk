import LfzkV2.OracleSampling
import LfzkV2.Nizk
import polygero.FiatShamir.CommittedComposition

/-!
# V2 frontend and backend on one adaptive random oracle

The backend term is proved for the compiled circuit statement and actual row
decoder. A fixed list near the commitment replaces the family of all polynomial
tuples; its exact size and outside-list query tail are both proved.
-/

namespace LfzkV2.ComposedFS

open SumcheckV2 RecursivePolygero Counting Finset Bcs.TotalOracle
open scoped Classical

variable {F C Q Out Key Context Parent Pad Slot : Type}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype C] [Nonempty C] [Fintype Q] [DecidableEq Q] [Fintype Parent]
variable {N L out input nPublic nPrivate : ℕ}

/-- A common-oracle composition with no assumption that the transcript-dependent
backend statement is false. Both stages see the same adaptive query tree. -/
theorem soundness_le
    (circuit : Circuit F out input)
    (index : (Fin nPublic ⊕ Fin nPrivate) ↪ Cube input)
    (publicInputs : Fin nPublic → F) (privateCoordinate : Fin nPrivate → Slot)
    (coordinate : Pad → Slot)
    (I : Instance F) (parameters : HahnSystemCertificate I)
    (hsmall : parameters.rankError ≤ 1/(Nat.card F : ℚ))
    (cutoff bound : ℕ) (hcutoff : I.r+I.w-1 < cutoff)
    (hpacking : CodingTheory.UniformFamilyBound I.n cutoff (I.r+I.w-1) bound)
    (setup : FiatShamir.OracleSetup F C Q Out Key Context (Fin bound) N L)
    (selected : Out → Parent × I.layer.Payload)
    (parent : Parent → Q) (child : Parent → I.layer.Payload → Q)
    (hparent : Function.Injective parent)
    (hchild : Function.Injective (fun i : Parent × I.layer.Payload => child i.1 i.2))
    (hdisjoint : ∀ j j' payload, parent j ≠ child j' payload)
    (view : Parent → (Q → C) → Reconstruction circuit Pad Slot)
    (oracle : Parent → (Q → C) → I.layer.Oracle)
    (hviewOff : ∀ j payload H H',
      (∀ z, z ≠ parent j → z ≠ child j payload → H z = H' z) → view j H = view j H')
    (horacleOff : ∀ j payload H H',
      (∀ z, z ≠ parent j → z ≠ child j payload → H z = H' z) → oracle j H = oracle j H')
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
      ¬ circuit.Satisfies (zeroExtend index (Sum.elim publicInputs privateInputs)))
    (hcover : ∀ H candidate,
      let j := (selected (setup.adversary.run H).1).1
      let g := committedCandidate I (oracle j H) cutoff bound candidate
      setup.Covers H candidate ((view j H).tests index publicInputs privateCoordinate coordinate
        (Backend.read ((tupleCounts I).witness g) ∘ Backend.linearAddress primary)))
    (maxBudget : ℕ) (hmax : ∀ x, setup.budget x ≤ maxBudget)
    (slotBudget : Fin L → ℕ)
    (hslot : ∀ result i, setup.budget (setup.hashInput result i.val) ≤ slotBudget i) :
    let accepts := fun H : Q → C =>
      let i := selected (setup.adversary.run H).1
      let v := view i.1 H
      I.layer.verify (v.backendStatement index publicInputs privateCoordinate coordinate
        I primary (product v) (eqns v)) (oracle i.1 H)
        (decodeCoin (H (parent i.1))) i.2 (decodeQuery (H (child i.1 i.2)))
    ((univ.filter accepts).card : ℚ)/(Fintype.card C : ℚ)^Fintype.card Q ≤
      (N+1 : ℕ)*(parameters.error + ((cutoff+I.s-1).choose I.t : ℚ)/I.n.choose I.t) + (bound : ℚ) *
        (N*maxBudget + ∑ i, slotBudget i)/Fintype.card F := by
  intro accepts
  let chosen := fun H : Q → C => selected (setup.adversary.run H).1
  let finalView := fun H => view (chosen H).1 H
  let statement := fun v : Reconstruction circuit Pad Slot =>
    v.backendStatement index publicInputs privateCoordinate coordinate I primary (product v) (eqns v)
  let family := fun H candidate => committedCandidate I (oracle (chosen H).1 H) cutoff bound candidate
  let frontend := fun H => ∃ candidate : Fin bound,
    (finalView H).Accepts index publicInputs privateCoordinate coordinate
      (Backend.read ((tupleCounts I).witness (family H candidate)) ∘ Backend.linearAddress primary)
  letI : DecidablePred frontend := fun _ => Classical.propDecidable _
  have hfront : ((univ.filter frontend).card : ℚ)/(Fintype.card C : ℚ)^Fintype.card Q ≤
      (bound : ℚ) *
        (N*maxBudget + ∑ i, slotBudget i)/Fintype.card F := by
    have h := setup.soundness_le maxBudget hmax slotBudget hslot frontend (by
      intro H hH
      obtain ⟨candidate, hg⟩ := hH
      exact ⟨candidate, _, hcover H candidate,
        (finalView H).accepts_false index publicInputs privateCoordinate coordinate _ hfalse hg⟩)
    simpa only [Fintype.card_fin] using h
  convert! NonrecursiveFS.committed_composition_le I parameters hsmall setup.adversary selected
    parent child hparent hchild hdisjoint (fun j H => (view j H, oracle j H))
    (by intro j payload H H' h; exact Prod.ext (hviewOff j payload H H' h) (horacleOff j payload H H' h))
    (fun s _ => statement s.1) (fun s _ => s.2)
    decodeCoin decodeQuery kCoin kQuery hcoin hquery hkCoin hkQuery cutoff bound hcutoff hpacking
    (fun H g => (finalView H).Accepts index publicInputs privateCoordinate coordinate
      (Backend.read ((tupleCounts I).witness g) ∘ Backend.linearAddress primary))
    (by
      intro H g
      dsimp only
      intro hdecode
      exact (finalView H).decoded_accepts index publicInputs privateCoordinate coordinate
        I primary (product (finalView H)) (eqns (finalView H)) (oracle (chosen H).1 H)
        (decodeCoin (H (parent (chosen H).1))) (chosen H).2 g hdecode)
    _ (by
      convert! hfront using 1
      congr 3
      ext H
      simp only [mem_filter, frontend, family, chosen]) using 1

end LfzkV2.ComposedFS
