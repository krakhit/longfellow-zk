import LfzkV2.TwoFieldFS
import LfzkV2.CommitmentFS

/-! The two authenticated V2 oracles use V1's common cut trace and joint
Merkle checking execution. Both are fixed before the first point naming
their common commitment key. The proof model carries a MAC-answer annotation
and the acceptance event checks its coherence with the oracle. -/

namespace LfzkV2.TwoFieldCommitmentFS

open RecursivePolygero Merkle Merkle.MH Bcs.TotalOracle
  Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree TwoFieldReplay
open scoped Classical

section Cut

variable {F C Key Q Out Enc D Salt : Type} [Field F] [Fintype F] [DecidableEq F]
variable [DecidableEq Q] [DecidableEq Key] [DecidableEq Enc] [DecidableEq D] [Inhabited D]
variable [Inhabited Salt] {tA N L TM : ℕ}
variable (I : Instance F) [Inhabited (MerkleCompiler.Leaf F I.nw I.nq)]
variable (S : Bcs.TotalOracleCommit.Setup Enc D Q C Out Key tA N L)
variable {codec : Codec Salt (MerkleCompiler.Leaf F I.nw I.nq) D Enc}
variable (dec : RoleDecoders codec) (rootOf : Key → D)

noncomputable def cutOracle (mt : Fin TM → D) (H : Q → C) (key : Key) : I.layer.Oracle :=
  let ctx := (S.atOracle H).ctxAt mt Bcs.TotalOracleCommit.Setup.emptyTape key
  MerkleCompiler.extractedOracle I dec (rootOf ctx.1) ctx.2

theorem cutOracle_off (mt : Fin TM → D) (H H' : Q → C) (x : Q) (hoff : AgreeOff x H H') :
    cutOracle I S dec rootOf mt H' (S.key x) = cutOracle I S dec rootOf mt H (S.key x) := by
  exact congrArg (fun ctx : Key × List (Enc × D) =>
    MerkleCompiler.extractedOracle I dec (rootOf ctx.1) ctx.2) (S.ctxAt_off mt H H' x hoff)

end Cut

variable {F₁ F₂ Key C Public Out Enc D Salt₁ Salt₂ : Type}
variable [Field F₁] [Fintype F₁] [DecidableEq F₁]
variable [Field F₂] [Fintype F₂] [DecidableEq F₂]
variable {out₁ input₁ out₂ input₂ tA N : ℕ}
variable (circuit₁ : Circuit F₁ out₁ input₁) (I₁ : Instance F₁)
variable (circuit₂ : Circuit F₂ out₂ input₂) (I₂ : Instance F₂)

def setup [DecidableEq (Domain Key C Public circuit₁ I₁ circuit₂ I₂)]
    (body : TwoOracleTree Enc D (Domain Key C Public circuit₁ I₁ circuit₂ I₂) C Out tA N)
    (proofOf : Out → Proof Key C Public circuit₁ I₁ circuit₂ I₂) (dflt : C) :
    Bcs.TotalOracleCommit.Setup Enc D (Domain Key C Public circuit₁ I₁ circuit₂ I₂) C Out Key tA N
      (1+(Replay.slots circuit₁+2)+(Replay.slots circuit₂+2)) where
  body := body
  hashInput out := hashInput circuit₁ I₁ circuit₂ I₂ (proofOf out)
  dflt := dflt
  key := key circuit₁ I₁ circuit₂ I₂
  keyOut out := (proofOf out).context.1
  hkey out k := hashInput_key circuit₁ I₁ circuit₂ I₂ (proofOf out) k

variable [DecidableEq Enc] [Inhabited D]
variable (codec₁ : Codec Salt₁ (MerkleCompiler.Leaf F₁ I₁.nw I₁.nq) D Enc)
variable (codec₂ : Codec Salt₂ (MerkleCompiler.Leaf F₂ I₂.nw I₂.nq) D Enc)
variable (claimOf₁ : Out → OpeningClaim I₁.n Salt₁ (MerkleCompiler.Leaf F₁ I₁.nw I₁.nq) D)
variable (claimOf₂ : Out → OpeningClaim I₂.n Salt₂ (MerkleCompiler.Leaf F₂ I₂.nw I₂.nq) D)

def check (out : Out) : Tree Enc D Unit (2*I₂.n+2*I₁.n) :=
  (CommitmentFS.merkleCheck I₁ codec₁ claimOf₁ out).bind
    (fun _ => CommitmentFS.merkleCheck I₂ codec₂ claimOf₂ out)

omit [Fintype F₁] [DecidableEq F₁] [Fintype F₂] [DecidableEq F₂] in
theorem check_contains_one (H : Enc → D) (out : Out) (qa : Enc × D)
    (hqa : qa ∈ ((checkPass codec₁ I₁.n (claimOf₁ out).I (claimOf₁ out).a
      (claimOf₁ out).pf (2*I₁.n) fun _ => default).run H).2) :
    qa ∈ ((check I₁ I₂ codec₁ codec₂ claimOf₁ claimOf₂ out).run H).2 := by
  simp only [check, Tree.run_bind, CommitmentFS.merkleCheck, Tree.run_map]
  exact List.mem_append_left _ hqa

omit [Fintype F₁] [DecidableEq F₁] [Fintype F₂] [DecidableEq F₂] in
theorem check_contains_two (H : Enc → D) (out : Out) (qa : Enc × D)
    (hqa : qa ∈ ((checkPass codec₂ I₂.n (claimOf₂ out).I (claimOf₂ out).a
      (claimOf₂ out).pf (2*I₂.n) fun _ => default).run H).2) :
    qa ∈ ((check I₁ I₂ codec₁ codec₂ claimOf₁ claimOf₂ out).run H).2 := by
  simp only [check, Tree.run_bind, CommitmentFS.merkleCheck, Tree.run_map]
  exact List.mem_append_right _ hqa

section Bound

open Finset

variable [Fintype C] [Fintype Key] [Fintype Public] [Fintype D]
variable [DecidableEq Key] [DecidableEq D] [Inhabited Salt₁] [Inhabited Salt₂]
variable [Inhabited (MerkleCompiler.Leaf F₁ I₁.nw I₁.nq)]
variable [Inhabited (MerkleCompiler.Leaf F₂ I₂.nw I₂.nq)]
variable [Fintype (Replay.Payload circuit₁)] [Fintype (Replay.Payload circuit₂)]
variable [DecidableEq (Domain Key C Public circuit₁ I₁ circuit₂ I₂)]
variable {Fmac : Type} [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {blocks TM : ℕ}
variable (S₁ : CompiledSide F₁ C (SideContext Key C Public) circuit₁ I₁)
variable (S₂ : CompiledSide F₂ C
  (SideContext Key C Public × FirstSnapshot Key C Public circuit₁ I₁) circuit₂ I₂)
variable (M : MacData C Fmac (Counting.tupleCounts I₁).Index (Counting.tupleCounts I₂).Index blocks)

/-- The annotated authenticated two-field verifier, using V1's two-opening
reduction and its single shared-query potential compiler. No backend
soundness or commitment-context invariance is left as a premise. -/
theorem extraction_le
    (ht₁ : 0 < I₁.t) (ht₂ : 0 < I₂.t)
    (body : TwoOracleTree Enc D (Domain Key C Public circuit₁ I₁ circuit₂ I₂) C Out tA N)
    (proofOf : Out → Proof Key C Public circuit₁ I₁ circuit₂ I₂)
    (dec₁ : RoleDecoders codec₁) (dec₂ : RoleDecoders codec₂)
    (rootOf₁ rootOf₂ : Key → D)
    (tag : Public → Fin blocks → Fmac)
    (hrowOne : ∀ (ctx : SideContext Key C Public) W g, S₁.Good ctx W g →
      M.macOne g (M.decode ctx.2.1) = tag ctx.2.2)
    (hrowTwo : ∀ (ctx : SideContext Key C Public × FirstSnapshot Key C Public circuit₁ I₁) W g,
      S₂.Good ctx W g → M.macTwo g (M.decode ctx.1.2.1) = tag ctx.1.2.2)
    (hspace : 2*I₂.n+2*I₁.n+tA ≤ TM) :
    let K := setup circuit₁ I₁ circuit₂ I₂ body proofOf S₁.dflt
    let ck := check I₁ I₂ codec₁ codec₂ claimOf₁ claimOf₂
    let context := fun (mt : Fin TM → D) (H : Domain Key C Public circuit₁ I₁ circuit₂ I₂ → C) key =>
      (cutOracle I₁ K dec₁ rootOf₁ mt H key,cutOracle I₂ K dec₂ rootOf₂ mt H key)
    let acceptedAt := fun (mt : Fin TM → D) (H : Domain Key C Public circuit₁ I₁ circuit₂ I₂ → C) (result : Out) =>
      let proof := proofOf result
      proof.context.2.1 = H (.inl proof.context.1) ∧
      S₁.CompiledAccepts Prod.fst Prod.snd ht₁ (codec₁.withOracle (K.merkleOracle ck mt H))
        (fun x => H (.inr (.inl x))) (selectedOne circuit₁ I₁ circuit₂ I₂ proof)
        (rootOf₁ proof.context.1) (claimOf₁ result) ∧
      S₂.CompiledAccepts Prod.fst Prod.snd ht₂ (codec₂.withOracle (K.merkleOracle ck mt H))
        (fun x => H (.inr (.inr x))) (selectedTwo circuit₁ I₁ circuit₂ I₂ proof)
        (rootOf₂ proof.context.1) (claimOf₂ result)
    let badAt := fun (mt : Fin TM → D) (H : Domain Key C Public circuit₁ I₁ circuit₂ I₂ → C) (result : Out) =>
      let proof := proofOf result
      let W := context mt H proof.context.1
      TwoFieldPotential.extract circuit₁ I₁ circuit₂ I₂ S₁ S₂ M W proof = none
    let accepts := fun mt H => acceptedAt mt H (K.proof mt H)
    let fails := fun mt H => badAt mt H (K.proof mt H)
    ((univ.filter fun ω : (Fin TM → D) × (Domain Key C Public circuit₁ I₁ circuit₂ I₂ → C) =>
        accepts ω.1 ω.2 ∧ fails ω.1 ω.2).card : ℚ) /
      ((Fintype.card D : ℚ)^TM * (Fintype.card C : ℚ)^Fintype.card (Domain Key C Public circuit₁ I₁ circuit₂ I₂)) ≤
      (N * TwoFieldFS.maxBudget circuit₁ I₁ circuit₂ I₂ S₁ S₂ M +
        ∑ i, TwoFieldFS.slotBudget circuit₁ I₁ circuit₂ I₂ S₁ S₂ M i)/Fintype.card C +
      2 * (Bcs.AdaptiveCommit.adaptiveNumerator (2*I₂.n+2*I₁.n) tA
        (1+(Replay.slots circuit₁+2)+(Replay.slots circuit₂+2)+N) : ℚ)/Fintype.card D := by
  letI : Nonempty C := ⟨S₁.dflt⟩
  intro K ck context acceptedAt badAt accepts fails
  let idealAt := fun (mt : Fin TM → D) (H : Domain Key C Public circuit₁ I₁ circuit₂ I₂ → C) (result : Out) =>
    let proof := proofOf result
    let W := context mt H proof.context.1
    proof.context.2.1 = H (.inl proof.context.1) ∧
    S₁.Accepts Prod.fst Prod.snd W.1 (fun x => H (.inr (.inl x))) (selectedOne circuit₁ I₁ circuit₂ I₂ proof) ∧
    S₂.Accepts Prod.fst Prod.snd W.2 (fun x => H (.inr (.inr x))) (selectedTwo circuit₁ I₁ circuit₂ I₂ proof) ∧
    badAt mt H result
  let fsError : ℚ := (N * TwoFieldFS.maxBudget circuit₁ I₁ circuit₂ I₂ S₁ S₂ M +
    ∑ i, TwoFieldFS.slotBudget circuit₁ I₁ circuit₂ I₂ S₁ S₂ M i)/Fintype.card C
  have hfs mt : ((univ.filter fun H => idealAt mt H (K.proof mt H)).card : ℚ)/
      (Fintype.card C : ℚ)^Fintype.card (Domain Key C Public circuit₁ I₁ circuit₂ I₂) ≤ fsError := by
    have h := TwoFieldFS.extraction_le circuit₁ I₁ circuit₂ I₂ S₁ S₂ M
      (K.search mt) proofOf (context mt)
      (by
        intro H H' x hoff
        exact Prod.ext (cutOracle_off I₁ K dec₁ rootOf₁ mt H H' x hoff)
          (cutOracle_off I₂ K dec₂ rootOf₂ mt H H' x hoff)) tag hrowOne hrowTwo
    convert! h using 1
    congr 3
    ext H
    simp only [mem_filter]
    change (H ∈ univ ∧ idealAt mt H (K.proof mt H)) ↔
      (H ∈ univ ∧ idealAt mt H ((K.search mt).run H).1)
    rw [K.proof_eq]
  have hbridge mt H (ha : accepts mt H)
      (he₁ : K.Explains dec₁ rootOf₁ claimOf₁ mt H)
      (he₂ : K.Explains dec₂ rootOf₂ claimOf₂ mt H) (hb : fails mt H) : idealAt mt H (K.proof mt H) := by
    obtain ⟨e₁,hext₁,hagree₁,-⟩ := he₁
    obtain ⟨e₂,hext₂,hagree₂,-⟩ := he₂
    let result := K.proof mt H
    let proof := proofOf result
    refine ⟨ha.1,?_,?_,hb⟩
    · exact S₁.accepts_of_extraction Prod.fst Prod.snd ht₁ dec₁
        (codec₁.withOracle (K.merkleOracle ck mt H)) (fun x => H (.inr (.inl x)))
        (selectedOne circuit₁ I₁ circuit₂ I₂ proof) (rootOf₁ proof.context.1)
        ((K.atOracle H).cutTrace mt Bcs.TotalOracleCommit.Setup.emptyTape proof.context.1)
        (claimOf₁ result) e₁ hext₁ hagree₁ ha.2.1
    · exact S₂.accepts_of_extraction Prod.fst Prod.snd ht₂ dec₂
        (codec₂.withOracle (K.merkleOracle ck mt H)) (fun x => H (.inr (.inr x)))
        (selectedTwo circuit₁ I₁ circuit₂ I₂ proof) (rootOf₂ proof.context.1)
        ((K.atOracle H).cutTrace mt Bcs.TotalOracleCommit.Setup.emptyTape proof.context.1)
        (claimOf₂ result) e₂ hext₂ hagree₂ ha.2.2
  have hTM : 1 ≤ TM := by have := I₁.query_le; omega
  have h := K.ratio_le_two_from_potential codec₁ dec₁ ck rootOf₁ claimOf₁
    (check_contains_one I₁ I₂ codec₁ codec₂ claimOf₁ claimOf₂)
    codec₂ dec₂ ck rootOf₂ claimOf₂ (check_contains_two I₁ I₂ codec₁ codec₂ claimOf₁ claimOf₂)
    (by omega) (by omega) hspace hTM accepts fails
    (fun _ _ h => h.2.1.2.1) (fun _ _ h => h.2.2.2.1) fsError (by
      intro mt
      apply le_trans _ (hfs mt)
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply (Nat.cast_le (α := ℚ)).mpr
      exact card_le_card (by
        intro H hH
        simp only [mem_filter] at hH
        exact mem_filter.mpr ⟨mem_univ _,hbridge mt H hH.2.1 hH.2.2.2.1 hH.2.2.1 hH.2.2.2.2⟩))
  convert! h using 1
  congr 3
  ext ω
  simp only [mem_filter]

end Bound

end LfzkV2.TwoFieldCommitmentFS
