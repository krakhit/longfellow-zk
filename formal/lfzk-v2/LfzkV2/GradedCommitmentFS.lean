import LfzkV2.CommitmentFS
import LfzkV2.GradedFS

/-! V1's Merkle binding reduction applied to the concrete graded V2 bound. -/

namespace LfzkV2.GradedCommitmentFS

open Finset SumcheckV2 RecursivePolygero NonrecursiveFS Merkle Merkle.MH
  Bcs.TotalOracle Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree CommitmentFS
open scoped Classical

variable {F C Key Parent Out Pad Slot Enc D Salt : Type}
variable [Field F] [Fintype F] [DecidableEq F]
variable {out input tA N TM : ℕ}

/-- The authenticated V2 verifier with V1's graded shared-oracle accounting.
The commitment context is extracted from the prover's actual cut trace. -/
theorem soundness_le [Fintype C] [Fintype Key] [Fintype Parent] [Fintype D]
    [DecidableEq Enc] [DecidableEq D] [Inhabited D] [Inhabited Salt]
    {nPublic nPrivate : ℕ}
    (circuit : Circuit F out input) (plan : Replay.PadPlan (Pad := Pad) (Slot := Slot) circuit)
    (sampling : Replay.Sampling F C circuit) (dflt : C)
    (index : (Fin nPublic ⊕ Fin nPrivate) ↪ Cube input)
    (publicInputs : Fin nPublic → F) (privateCoordinate : Fin nPrivate → Slot)
    (coordinate : Pad → Slot)
    (I : Instance F) (ht : 0 < I.t) [Inhabited (MerkleCompiler.Leaf F I.nw I.nq)]
    (cutoff bound : ℕ) (hcutoff : I.r+I.w-1 < cutoff)
    (hpacking : CodingTheory.UniformFamilyBound I.n cutoff (I.r+I.w-1) bound)
    (body : TwoOracleTree Enc D (ConcreteFS.Domain Key circuit I Parent) C Out tA N)
    (selected : Out → Parent × I.layer.Payload)
    (keyOf : Parent → Key) (payloadOf : Parent → Replay.Payload circuit)
    (primary : Slot → Fin I.nw × Fin I.q)
    (product : (v : Reconstruction circuit Pad Slot) →
      Fin v.constraints.layers.length → Fin I.nq × Fin I.q)
    (eqns : (v : Reconstruction circuit Pad Slot) → I.Equations ≃ Backend.Equation
      (v.rows index publicInputs privateCoordinate coordinate).length v.constraints.layers.length)
    (decodeCoin : C → I.layer.Coin) (decodeQuery : C → I.layer.Query)
    (P : TerminalPotential I cutoff decodeCoin decodeQuery)
    (codec : Codec Salt (MerkleCompiler.Leaf F I.nw I.nq) D Enc) (dec : RoleDecoders codec)
    (rootOf : Key → D)
    (claimOf : Out → OpeningClaim I.n Salt (MerkleCompiler.Leaf F I.nw I.nq) D)
    (hspace : 2*I.n+tA ≤ TM)
    (hfalse : ∀ privateInputs : Fin nPrivate → F,
      ¬ circuit.Satisfies (zeroExtend index (Sum.elim publicInputs privateInputs))) :
    let S := setup circuit I body dflt selected keyOf payloadOf
    let check := merkleCheck I codec claimOf
    let accepts := fun ω : (Fin TM → D) × (ConcreteFS.Domain Key circuit I Parent → C) =>
      let result := S.proof ω.1 ω.2
      let i := selected result
      let v := Replay.reconstruction sampling.decode circuit plan (keyOf i.1) (payloadOf i.1) ω.2
      (MerkleCompiler.compiler I ht).Accepts (codec.withOracle (S.merkleOracle check ω.1 ω.2))
        (v.backendStatement index publicInputs privateCoordinate coordinate I primary (product v) (eqns v))
        (rootOf (keyOf i.1)) (decodeCoin (ω.2 (ConcreteFS.parent circuit I i.1))) i.2
          (decodeQuery (ω.2 (ConcreteFS.child circuit I i.1 i.2))) (claimOf result)
    ((univ.filter accepts).card : ℚ) /
        ((Fintype.card D : ℚ)^TM * (Fintype.card C : ℚ)^Fintype.card (ConcreteFS.Domain Key circuit I Parent)) ≤
      (Bcs.AdaptiveCommit.adaptiveNumerator (2*I.n) tA (Replay.slots circuit+2+N) : ℚ)/Fintype.card D +
        (N * GradedFS.maxBudget (bound := bound) circuit I sampling P +
          ∑ i : Fin (Replay.slots circuit+2), GradedFS.slotBudget (bound := bound) circuit I sampling P i)/Fintype.card C := by
  letI : Nonempty C := ⟨dflt⟩
  intro S check accepts
  let acceptedAt := fun (mt : Fin TM → D) (H : ConcreteFS.Domain Key circuit I Parent → C) (result : Out) =>
    let i := selected result
    let v := Replay.reconstruction sampling.decode circuit plan (keyOf i.1) (payloadOf i.1) H
    I.layer.verify
      (v.backendStatement index publicInputs privateCoordinate coordinate I primary (product v) (eqns v))
      (cutOracle circuit I S dec rootOf mt H (keyOf i.1))
      (decodeCoin (H (ConcreteFS.parent circuit I i.1))) i.2
      (decodeQuery (H (ConcreteFS.child circuit I i.1 i.2)))
  let ideal := fun mt H => acceptedAt mt H (S.proof mt H)
  let fsError : ℚ := (N * GradedFS.maxBudget (bound := bound) circuit I sampling P +
    ∑ i : Fin (Replay.slots circuit+2), GradedFS.slotBudget (bound := bound) circuit I sampling P i)/Fintype.card C
  have hfs mt : ((univ.filter (ideal mt)).card : ℚ)/
      (Fintype.card C : ℚ)^Fintype.card (ConcreteFS.Domain Key circuit I Parent) ≤ fsError := by
    have h := GradedFS.compiled_soundness_le circuit I plan sampling dflt keyOf payloadOf P
      index publicInputs privateCoordinate coordinate primary product eqns hcutoff hpacking
      (S.search mt) selected (cutOracle circuit I S dec rootOf mt)
      (by intro H H' x hoff; exact cutOracle_off circuit I S dec rootOf mt H H' x hoff) hfalse
    convert! h using 1
    congr 3
    ext H
    simp only [mem_filter]
    change (H ∈ univ ∧ acceptedAt mt H (S.proof mt H)) ↔
      (H ∈ univ ∧ acceptedAt mt H ((S.search mt).run H).1)
    rw [S.proof_eq]
  have hbridge mt H (hacc : accepts (mt,H)) (hexp : S.Explains dec rootOf claimOf mt H) : ideal mt H := by
    obtain ⟨e,hext,hagree,-⟩ := hexp
    let result := S.proof mt H
    let i := selected result
    let v := Replay.reconstruction sampling.decode circuit plan (keyOf i.1) (payloadOf i.1) H
    exact MerkleCompiler.verify_of_extraction I ht dec (codec.withOracle (S.merkleOracle check mt H))
      (v.backendStatement index publicInputs privateCoordinate coordinate I primary (product v) (eqns v))
      (rootOf (keyOf i.1)) ((S.atOracle H).cutTrace mt Bcs.TotalOracleCommit.Setup.emptyTape (keyOf i.1))
      (decodeCoin (H (ConcreteFS.parent circuit I i.1))) i.2
      (decodeQuery (H (ConcreteFS.child circuit I i.1 i.2))) (claimOf result) e hext hagree hacc
  have hTM : 1 ≤ TM := by have := I.query_le; omega
  have h := S.ratio_le_from_potential codec dec check rootOf claimOf
    (by intro H result qa hqa; simpa only [check, merkleCheck, Tree.run_map] using hqa)
    (by omega) (by omega) hspace hTM
    (fun mt H => accepts (mt,H)) (fun _ _ => True) (fun _ _ hacc => hacc.2.1) fsError (by
      intro mt
      apply le_trans _ (hfs mt)
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply (Nat.cast_le (α := ℚ)).mpr
      exact card_le_card (by
        intro H hH
        simp only [mem_filter] at hH
        exact mem_filter.mpr ⟨mem_univ _,hbridge mt H hH.2.1 hH.2.2.1⟩))
  have h' : ((univ.filter accepts).card : ℚ) /
      ((Fintype.card D : ℚ)^TM * (Fintype.card C : ℚ)^Fintype.card (ConcreteFS.Domain Key circuit I Parent)) ≤
      fsError + (Bcs.AdaptiveCommit.adaptiveNumerator (2*I.n) tA (Replay.slots circuit+2+N) : ℚ)/Fintype.card D := by
    convert! h using 1
    congr 3
    ext ω
    simp only [mem_filter, and_true]
  exact h'.trans_eq (by dsimp only [fsError]; ring)

end LfzkV2.GradedCommitmentFS
