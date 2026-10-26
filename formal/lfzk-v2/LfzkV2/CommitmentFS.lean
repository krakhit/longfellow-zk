import LfzkV2.ConcreteFS
import polygero.FiatShamir.MerkleCompiler
import Bcs.TotalOracleCommit
import Bcs.PotentialCommit

/-! V2 commitment contexts are the existing Merkle cut traces, taken before
the first oracle query naming that commitment. Their frontend and backend
resampling properties follow from V1's generic commitment theorem. -/

namespace LfzkV2.CommitmentFS

open SumcheckV2 RecursivePolygero Merkle Merkle.MH
open Bcs.TotalOracle Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree
open scoped Classical

variable {F C Key Parent Out Pad Slot Enc D Salt : Type}
variable [Field F] [Fintype F] [DecidableEq F]
variable {out input tA N TM : ℕ}

def setup (circuit : Circuit F out input) (I : Instance F)
    (body : TwoOracleTree Enc D (ConcreteFS.Domain Key circuit I Parent) C Out tA N)
    (dflt : C) (selected : Out → Parent × I.layer.Payload)
    (keyOf : Parent → Key) (payloadOf : Parent → Replay.Payload circuit) :
    Bcs.TotalOracleCommit.Setup Enc D (ConcreteFS.Domain Key circuit I Parent) C Out Key tA N
      (Replay.slots circuit + 2) where
  body := body
  hashInput result k :=
    let i := selected result
    if k < Replay.slots circuit then
      .inl (Replay.hashInput circuit (keyOf i.1) (payloadOf i.1) k)
    else if k = Replay.slots circuit then ConcreteFS.parent circuit I i.1
    else ConcreteFS.child circuit I i.1 i.2
  dflt := dflt
  key := Replay.queryKey circuit (ConcreteFS.roleKey I keyOf)
  keyOut result := keyOf (selected result).1
  hkey result k := by
    dsimp
    split_ifs
    · exact Replay.hashInput_key circuit _ _ _
    · rfl
    · rfl

section Cut

variable [DecidableEq Enc] [DecidableEq D] [Inhabited D] [Inhabited Salt]
variable (circuit : Circuit F out input) (I : Instance F)
variable [Inhabited (MerkleCompiler.Leaf F I.nw I.nq)]
variable {L : ℕ}
variable (S : Bcs.TotalOracleCommit.Setup Enc D (ConcreteFS.Domain Key circuit I Parent) C Out Key tA N L)
variable {codec : Codec Salt (MerkleCompiler.Leaf F I.nw I.nq) D Enc}
variable (dec : RoleDecoders codec) (rootOf : Key → D)

noncomputable def cutOracle (mt : Fin TM → D) (H : ConcreteFS.Domain Key circuit I Parent → C)
    (key : Key) : I.layer.Oracle :=
  let ctx := (S.atOracle H).ctxAt mt Bcs.TotalOracleCommit.Setup.emptyTape key
  MerkleCompiler.extractedOracle I dec (rootOf ctx.1) ctx.2

theorem cutOracle_off (mt : Fin TM → D) (H H' : ConcreteFS.Domain Key circuit I Parent → C)
    (x : ConcreteFS.Domain Key circuit I Parent) (hoff : AgreeOff x H H') :
    cutOracle circuit I S dec rootOf mt H' (S.key x) =
      cutOracle circuit I S dec rootOf mt H (S.key x) := by
  exact congrArg (fun ctx : Key × List (Enc × D) =>
    MerkleCompiler.extractedOracle I dec (rootOf ctx.1) ctx.2) (S.ctxAt_off mt H H' x hoff)

end Cut

def merkleCheck [DecidableEq Enc] [Inhabited D] (I : Instance F)
    (codec : Codec Salt (MerkleCompiler.Leaf F I.nw I.nq) D Enc)
    (claimOf : Out → OpeningClaim I.n Salt (MerkleCompiler.Leaf F I.nw I.nq) D)
    (result : Out) : Tree Enc D Unit (2*I.n) :=
  (checkPass codec I.n (claimOf result).I (claimOf result).a (claimOf result).pf (2*I.n)
    fun _ => default).map fun _ => ()

/-- The compiled V2 verifier against one re-committing prover. Merkle binding,
the commitment-context invariants, concrete frontend replay, and Polygero
decoding are all reductions, rather than soundness premises. -/
theorem soundness_le [Fintype C] [Fintype Key] [Fintype Parent] [Fintype D]
    [DecidableEq Enc] [DecidableEq D] [Inhabited D] [Inhabited Salt]
    {nPublic nPrivate : ℕ}
    (circuit : Circuit F out input) (plan : Replay.PadPlan (Pad := Pad) (Slot := Slot) circuit)
    (sampling : Replay.Sampling F C circuit) (dflt : C)
    (index : (Fin nPublic ⊕ Fin nPrivate) ↪ Cube input)
    (publicInputs : Fin nPublic → F) (privateCoordinate : Fin nPrivate → Slot)
    (coordinate : Pad → Slot)
    (I : Instance F) (ht : 0 < I.t) [Inhabited (MerkleCompiler.Leaf F I.nw I.nq)]
    (parameters : HahnSystemCertificate I)
    (hsmall : parameters.rankError ≤ 1/(Nat.card F : ℚ))
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
    [DecidableEq I.layer.Coin] [DecidableEq I.layer.Query]
    (decodeCoin : C → I.layer.Coin) (decodeQuery : C → I.layer.Query)
    (kCoin kQuery : ℕ)
    (hcoin : ∀ coin, (Finset.univ.filter fun a : C => decodeCoin a = coin).card ≤ kCoin)
    (hquery : ∀ query, (Finset.univ.filter fun b : C => decodeQuery b = query).card ≤ kQuery)
    (hkCoin : kCoin*Fintype.card I.layer.Coin ≤ Fintype.card C)
    (hkQuery : kQuery*Fintype.card I.layer.Query ≤ Fintype.card C)
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
    ((Finset.univ.filter accepts).card : ℚ) /
        ((Fintype.card D : ℚ)^TM * (Fintype.card C : ℚ)^Fintype.card (ConcreteFS.Domain Key circuit I Parent)) ≤
      (Bcs.AdaptiveCommit.adaptiveNumerator (2*I.n) tA (Replay.slots circuit+2+N) : ℚ)/Fintype.card D +
        (N+1 : ℕ)*(parameters.error + ((cutoff+I.s-1).choose I.t : ℚ)/I.n.choose I.t) +
          (bound : ℚ)*(N*max out 2 + ∑ i : Fin (Replay.slots circuit),
            (Replay.roleKind circuit ((Replay.roleEquiv circuit).symm i)).budget)/Fintype.card F := by
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
  let fsError : ℚ :=
    (N+1 : ℕ)*(parameters.error + ((cutoff+I.s-1).choose I.t : ℚ)/I.n.choose I.t) +
      (bound : ℚ)*(N*max out 2 + ∑ i : Fin (Replay.slots circuit),
        (Replay.roleKind circuit ((Replay.roleEquiv circuit).symm i)).budget)/Fintype.card F
  have hfs mt : ((Finset.univ.filter (ideal mt)).card : ℚ)/
      (Fintype.card C : ℚ)^Fintype.card (ConcreteFS.Domain Key circuit I Parent) ≤ fsError := by
    have h := ConcreteFS.soundness_le circuit plan sampling dflt index publicInputs privateCoordinate
      coordinate I parameters hsmall cutoff bound hcutoff hpacking (S.search mt) selected keyOf payloadOf
      (cutOracle circuit I S dec rootOf mt)
      (by intro H H' x hoff; exact cutOracle_off circuit I S dec rootOf mt H H' x hoff)
      primary product eqns decodeCoin decodeQuery kCoin kQuery hcoin hquery hkCoin hkQuery hfalse
    convert! h using 1
    congr 3
    ext H
    simp only [Finset.mem_filter]
    change (H ∈ Finset.univ ∧ acceptedAt mt H (S.proof mt H)) ↔
      (H ∈ Finset.univ ∧ acceptedAt mt H ((S.search mt).run H).1)
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
      exact Finset.card_le_card (by
        intro H hH
        simp only [Finset.mem_filter] at hH
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hbridge mt H hH.2.1 hH.2.2.1⟩))
  have h' : ((Finset.univ.filter accepts).card : ℚ) /
      ((Fintype.card D : ℚ)^TM * (Fintype.card C : ℚ)^Fintype.card (ConcreteFS.Domain Key circuit I Parent)) ≤
      fsError + (Bcs.AdaptiveCommit.adaptiveNumerator (2*I.n) tA (Replay.slots circuit+2+N) : ℚ)/Fintype.card D := by
    convert! h using 1
    congr 3
    ext ω
    simp only [Finset.mem_filter, and_true]
  exact h'.trans_eq (by dsimp only [fsError]; ring)

end LfzkV2.CommitmentFS
