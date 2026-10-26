import LfzkV2.RuntimeExtraction
import LfzkV2.TwoFieldKeyReplay
import Bcs.SmallMerkle

/-! Authenticated extraction for raw proofs. The verifier appends its MAC-key
lookup and annotates the proof with that answer; key coherence is derived.
Counting this lookup as one additional query and bounding small-query Merkle
acceptance gives a unit-offset 117-bit bound for all prover budgets. -/

namespace LfzkV2.RawRuntimeExtraction

open Finset RecursivePolygero Merkle Merkle.MH Merkle.RandomOracle TwoFieldReplay RuntimeProfiles
open scoped Classical

variable {F₁ F₂ Key C Public Out Enc D Salt₁ Salt₂ Fmac : Type}
variable [Field F₁] [Fintype F₁] [DecidableEq F₁]
variable [Field F₂] [Fintype F₂] [DecidableEq F₂]
variable [Fintype C] [DecidableEq Enc] [Inhabited D]
variable [Field Fmac] [Fintype Fmac] [DecidableEq Fmac]
variable {out₁ input₁ out₂ input₂ blocks tA N TM : ℕ}
variable (circuit₁ : Circuit F₁ out₁ input₁) (I₁ : Instance F₁)
variable (circuit₂ : Circuit F₂ out₂ input₂) (I₂ : Instance F₂)
variable [Inhabited Salt₁] [Inhabited Salt₂]
variable [DecidableEq (Domain Key C Public circuit₁ I₁ circuit₂ I₂)]
variable (S₁ : CompiledSide F₁ C (SideContext Key C Public) circuit₁ I₁)
variable (S₂ : CompiledSide F₂ C
  (SideContext Key C Public × FirstSnapshot Key C Public circuit₁ I₁) circuit₂ I₂)
variable (M : MacData C Fmac (Counting.tupleCounts I₁).Index (Counting.tupleCounts I₂).Index blocks)
variable (geometry₁ : Geometry Hash.profile I₁) (geometry₂ : Geometry Signature.profile I₂)
variable (sampling₁ : BackendSampling I₁ S₁.decodeCoin S₁.decodeQuery)
variable (sampling₂ : BackendSampling I₂ S₂.decodeCoin S₂.decodeQuery)
variable (codec₁ : Codec Salt₁ (MerkleCompiler.Leaf F₁ I₁.nw I₁.nq) D Enc)
variable (codec₂ : Codec Salt₂ (MerkleCompiler.Leaf F₂ I₂.nw I₂.nq) D Enc)
variable (claimOf₁ : Out → OpeningClaim I₁.n Salt₁ (MerkleCompiler.Leaf F₁ I₁.nw I₁.nq) D)
variable (claimOf₂ : Out → OpeningClaim I₂.n Salt₂ (MerkleCompiler.Leaf F₂ I₂.nw I₂.nq) D)
variable (ht₁ : 0 < I₁.t) (ht₂ : 0 < I₂.t)
variable (body : TwoOracleTree Enc D (Domain Key C Public circuit₁ I₁ circuit₂ I₂) C Out tA N)
variable (proofOf : Out → RawProof (Key := Key) (Public := Public) circuit₁ I₁ circuit₂ I₂)
variable (dec₁ : RoleDecoders codec₁) (dec₂ : RoleDecoders codec₂) (rootOf₁ rootOf₂ : Key → D)

/-- The replayed answer is coherent for every oracle pair, even if the
original prover never queried the key. -/
theorem key_coherent (mt : Fin TM → D)
    (H : Domain Key C Public circuit₁ I₁ circuit₂ I₂ → C) :
    let K := TwoFieldCommitmentFS.setup circuit₁ I₁ circuit₂ I₂
      (prepareBody circuit₁ I₁ circuit₂ I₂ body proofOf)
      (preparedProof circuit₁ I₁ circuit₂ I₂ proofOf) S₁.dflt
    let proof := preparedProof circuit₁ I₁ circuit₂ I₂ proofOf (K.proof mt H)
    proof.context.2.1 = H (.inl proof.context.1) := by
  dsimp only
  rw [Bcs.TotalOracleCommit.Setup.proof_eq]
  simpa only [Bcs.TotalOracleCommit.Setup.search,TwoFieldCommitmentFS.setup,prepareBody_fixLeft] using
    preparedProof_coherent circuit₁ I₁ circuit₂ I₂
      (TwoOracleTree.fixLeft mt default body []) proofOf H

variable [Fintype Key] [Fintype Public] [Fintype D] [DecidableEq Key] [DecidableEq D]
variable [Inhabited (MerkleCompiler.Leaf F₁ I₁.nw I₁.nq)]
variable [Inhabited (MerkleCompiler.Leaf F₂ I₂.nw I₂.nq)]
variable [Fintype (Replay.Payload circuit₁)] [Fintype (Replay.Payload circuit₂)]

/-- Acceptance and paired-extraction failure after the verifier recomputes
the key. This event has no supplied-key coherence condition. -/
noncomputable def probability : ℚ :=
  let T₁ := S₁.withProfile Hash.profile geometry₁ sampling₁
  let T₂ := S₂.withProfile Signature.profile geometry₂ sampling₂
  let K := TwoFieldCommitmentFS.setup circuit₁ I₁ circuit₂ I₂
    (prepareBody circuit₁ I₁ circuit₂ I₂ body proofOf)
    (preparedProof circuit₁ I₁ circuit₂ I₂ proofOf) S₁.dflt
  let ck := TwoFieldCommitmentFS.check I₁ I₂ codec₁ codec₂
    (fun result : Out × C => claimOf₁ result.1) (fun result : Out × C => claimOf₂ result.1)
  let fails := fun ω : (Fin TM → D) × (Domain Key C Public circuit₁ I₁ circuit₂ I₂ → C) =>
    let result := K.proof ω.1 ω.2
    let proof := preparedProof circuit₁ I₁ circuit₂ I₂ proofOf result
    let W := (TwoFieldCommitmentFS.cutOracle I₁ K dec₁ rootOf₁ ω.1 ω.2 proof.context.1,
      TwoFieldCommitmentFS.cutOracle I₂ K dec₂ rootOf₂ ω.1 ω.2 proof.context.1)
    T₁.CompiledAccepts Prod.fst Prod.snd ht₁ (codec₁.withOracle (K.merkleOracle ck ω.1 ω.2))
      (fun x => ω.2 (.inr (.inl x))) (selectedOne circuit₁ I₁ circuit₂ I₂ proof)
      (rootOf₁ proof.context.1) (claimOf₁ result.1) ∧
    T₂.CompiledAccepts Prod.fst Prod.snd ht₂ (codec₂.withOracle (K.merkleOracle ck ω.1 ω.2))
      (fun x => ω.2 (.inr (.inr x))) (selectedTwo circuit₁ I₁ circuit₂ I₂ proof)
      (rootOf₂ proof.context.1) (claimOf₂ result.1) ∧
    TwoFieldPotential.extract circuit₁ I₁ circuit₂ I₂ T₁ T₂ M W proof = none
  ((univ.filter fails).card : ℚ) /
    ((Fintype.card D : ℚ)^TM * (Fintype.card C : ℚ)^Fintype.card (Domain Key C Public circuit₁ I₁ circuit₂ I₂))

/-- Derived key coherence removes the extra conjunct in the annotated
experiment. Both experiments use the same authenticated execution. -/
theorem probability_eq_annotated :
    probability (TM := TM) circuit₁ I₁ circuit₂ I₂ S₁ S₂ M geometry₁ geometry₂ sampling₁ sampling₂
      codec₁ codec₂ claimOf₁ claimOf₂ ht₁ ht₂ body proofOf dec₁ dec₂ rootOf₁ rootOf₂ =
    RuntimeExtraction.probability (TM := TM) circuit₁ I₁ circuit₂ I₂ S₁ S₂ M
      geometry₁ geometry₂ sampling₁ sampling₂ codec₁ codec₂
      (fun result : Out × C => claimOf₁ result.1) (fun result : Out × C => claimOf₂ result.1)
      ht₁ ht₂ (prepareBody circuit₁ I₁ circuit₂ I₂ body proofOf)
      (preparedProof circuit₁ I₁ circuit₂ I₂ proofOf) dec₁ dec₂ rootOf₁ rootOf₂ := by
  unfold probability RuntimeExtraction.probability TwoFieldCommitmentFS.failureProbability
  apply congrArg (fun s : Finset ((Fin TM → D) ×
      (Domain Key C Public circuit₁ I₁ circuit₂ I₂ → C)) =>
    (s.card : ℚ) / ((Fintype.card D : ℚ)^TM *
      (Fintype.card C : ℚ)^Fintype.card (Domain Key C Public circuit₁ I₁ circuit₂ I₂)))
  ext ω
  have hc := key_coherent circuit₁ I₁ circuit₂ I₂ S₁ body proofOf ω.1 ω.2
  dsimp only at hc
  simp only [mem_filter,and_assoc]
  tauto

theorem probability_le_one :
    probability (TM := TM) circuit₁ I₁ circuit₂ I₂ S₁ S₂ M geometry₁ geometry₂ sampling₁ sampling₂
      codec₁ codec₂ claimOf₁ claimOf₂ ht₁ ht₂ body proofOf dec₁ dec₂ rootOf₁ rootOf₂ ≤ 1 := by
  rw [probability_eq_annotated]
  exact RuntimeExtraction.probability_le_one circuit₁ I₁ circuit₂ I₂ S₁ S₂ M
    geometry₁ geometry₂ sampling₁ sampling₂ codec₁ codec₂
    (fun result : Out × C => claimOf₁ result.1) (fun result : Out × C => claimOf₂ result.1)
    ht₁ ht₂ (prepareBody circuit₁ I₁ circuit₂ I₂ body proofOf)
    (preparedProof circuit₁ I₁ circuit₂ I₂ proofOf) dec₁ dec₂ rootOf₁ rootOf₂

/-- With fewer than eight Merkle queries, authenticated acceptance already
requires a predictable digest hit. This bound is independent of the number
of transcript queries and does not assume distinct leaf encodings. -/
theorem probability_small_merkle (hsmall : tA < 8)
    (hspace : 2*I₂.n+2*I₁.n+tA ≤ TM) :
    probability (TM := TM) circuit₁ I₁ circuit₂ I₂ S₁ S₂ M geometry₁ geometry₂ sampling₁ sampling₂
      codec₁ codec₂ claimOf₁ claimOf₂ ht₁ ht₂ body proofOf dec₁ dec₂ rootOf₁ rootOf₂ ≤
      (2*tA*tA+(2*I₂.n+2*I₁.n+tA)*(2*tA+1) : ℕ)/(Fintype.card D : ℚ) := by
  letI : Nonempty C := ⟨S₁.dflt⟩
  let K := TwoFieldCommitmentFS.setup circuit₁ I₁ circuit₂ I₂
    (prepareBody circuit₁ I₁ circuit₂ I₂ body proofOf)
    (preparedProof circuit₁ I₁ circuit₂ I₂ proofOf) S₁.dflt
  let ck := TwoFieldCommitmentFS.check I₁ I₂ codec₁ codec₂
    (fun result : Out × C => claimOf₁ result.1) (fun result : Out × C => claimOf₂ result.1)
  have hn : 128 ≤ I₁.n := by rw [geometry₁.n]; decide
  have hTM : 1 ≤ TM := by omega
  have h := K.merkle_small_ratio_le codec₁ dec₁ ck rootOf₁
    (fun result : Out × C => claimOf₁ result.1)
    (TwoFieldCommitmentFS.check_contains_one I₁ I₂ codec₁ codec₂
      (fun result : Out × C => claimOf₁ result.1) (fun result : Out × C => claimOf₂ result.1))
    hsmall hn (by omega) hspace hTM
  refine le_trans ?_ h
  unfold probability
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply (Nat.cast_le (α := ℚ)).mpr
  apply card_le_card
  intro ω hω
  simp only [mem_filter] at hω ⊢
  exact ⟨hω.1,hω.2.1.2.1⟩

/-- Numbered leaf inputs strengthen the query threshold to all 87 opened
hash columns. No transcript-query factor enters the digest-guessing bound. -/
theorem probability_numbered_merkle
    (hnumbered : ∀ out, (claimOf₁ out).DistinctLeafInputs codec₁)
    (hsmall : tA < 87) (hspace : 2*I₂.n+2*I₁.n+tA ≤ TM) :
    probability (TM := TM) circuit₁ I₁ circuit₂ I₂ S₁ S₂ M geometry₁ geometry₂ sampling₁ sampling₂
      codec₁ codec₂ claimOf₁ claimOf₂ ht₁ ht₂ body proofOf dec₁ dec₂ rootOf₁ rootOf₂ ≤
      ((2*I₂.n+2*I₁.n+tA)*(2*tA+1) : ℕ)/(Fintype.card D : ℚ) := by
  letI : Nonempty C := ⟨S₁.dflt⟩
  let K := TwoFieldCommitmentFS.setup circuit₁ I₁ circuit₂ I₂
    (prepareBody circuit₁ I₁ circuit₂ I₂ body proofOf)
    (preparedProof circuit₁ I₁ circuit₂ I₂ proofOf) S₁.dflt
  let ck := TwoFieldCommitmentFS.check I₁ I₂ codec₁ codec₂
    (fun result : Out × C => claimOf₁ result.1) (fun result : Out × C => claimOf₂ result.1)
  have hTM : 1 ≤ TM := by have := I₁.query_le; omega
  have h := K.merkle_numbered_ratio_le codec₁ dec₁ ck rootOf₁
    (fun result : Out × C => claimOf₁ result.1)
    (TwoFieldCommitmentFS.check_contains_one I₁ I₂ codec₁ codec₂
      (fun result : Out × C => claimOf₁ result.1) (fun result : Out × C => claimOf₂ result.1))
    hspace hTM
  refine le_trans ?_ h
  unfold probability
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply (Nat.cast_le (α := ℚ)).mpr
  apply card_le_card
  intro ω hω
  simp only [mem_filter] at hω ⊢
  refine ⟨hω.1,hω.2.1.2.1,hnumbered _,?_⟩
  have hI := hω.2.1.1
  rw [hI]
  simpa only [MerkleCompiler.compiler,LigeroFamily.QuerySet.card_coordinates,
    geometry₁.t,Hash.profile] using hsmall

variable (hfield₁ : 2^128 ≤ Fintype.card F₁) (hfield₂ : 2^255 ≤ Fintype.card F₂)
variable (hmac : 2^128 ≤ Fintype.card Fmac) (hDigest : Fintype.card D = 2^256)
variable (hout₁ : out₁ ≤ 5) (hout₂ : out₂ ≤ 3)
variable (hfront₁ : out₁+circuit₁.sharpLayerBudget ≤ 655) (hfront₂ : out₂+circuit₂.sharpLayerBudget ≤ 552)
variable (tag : Public → Fin blocks → Fmac)
variable (hrowOne : ∀ (ctx : SideContext Key C Public) W g,
  (S₁.withProfile Hash.profile geometry₁ sampling₁).Good ctx W g →
    M.macOne g (M.decode ctx.2.1) = tag ctx.2.2)
variable (hrowTwo : ∀ (ctx : SideContext Key C Public × FirstSnapshot Key C Public circuit₁ I₁) W g,
  (S₂.withProfile Signature.profile geometry₂ sampling₂).Good ctx W g →
    M.macTwo g (M.decode ctx.1.2.1) = tag ctx.1.2.2)
variable (hspace : 2*I₂.n+2*I₁.n+tA ≤ TM)

include hfield₁ hfield₂ hmac hDigest hout₁ hout₂ hfront₁ hfront₂ tag hrowOne hrowTwo hspace

/-- The exact finite bound retains the one verifier lookup as an additive
query, with no supplied-key premise. -/
theorem probability_bound :
    probability (TM := TM) circuit₁ I₁ circuit₂ I₂ S₁ S₂ M geometry₁ geometry₂ sampling₁ sampling₂
      codec₁ codec₂ claimOf₁ claimOf₂ ht₁ ht₂ body proofOf dec₁ dec₂ rootOf₁ rootOf₂ ≤
      (1+N : ℕ)*RuntimeCost.coefficient+RuntimeCost.constant+
        2*(Bcs.AdaptiveCommit.adaptiveNumerator 12992 tA
          (1+(Replay.slots circuit₁+2)+(Replay.slots circuit₂+2)+(1+N)) : ℚ)/(2^256 : ℚ) := by
  rw [probability_eq_annotated]
  exact RuntimeExtraction.probability_bound circuit₁ I₁ circuit₂ I₂ S₁ S₂ M geometry₁ geometry₂ sampling₁ sampling₂
    codec₁ codec₂ (fun result : Out × C => claimOf₁ result.1) (fun result : Out × C => claimOf₂ result.1)
    ht₁ ht₂ (prepareBody circuit₁ I₁ circuit₂ I₂ body proofOf)
    (preparedProof circuit₁ I₁ circuit₂ I₂ proofOf) dec₁ dec₂ rootOf₁ rootOf₂
    hfield₁ hfield₂ hmac hDigest hout₁ hout₂ hfront₁ hfront₂ tag hrowOne hrowTwo hspace

/-- All prover-query budgets, with the explicit verifier-lookup offset. -/
theorem extraction_114 :
    probability (TM := TM) circuit₁ I₁ circuit₂ I₂ S₁ S₂ M geometry₁ geometry₂ sampling₁ sampling₂
      codec₁ codec₂ claimOf₁ claimOf₂ ht₁ ht₂ body proofOf dec₁ dec₂ rootOf₁ rootOf₂ ≤
      (2+N+tA : ℚ)/(2^114 : ℚ) := by
  rw [probability_eq_annotated]
  have h := RuntimeExtraction.extraction_114 circuit₁ I₁ circuit₂ I₂ S₁ S₂ M geometry₁ geometry₂ sampling₁ sampling₂
    codec₁ codec₂ (fun result : Out × C => claimOf₁ result.1) (fun result : Out × C => claimOf₂ result.1)
    ht₁ ht₂ (prepareBody circuit₁ I₁ circuit₂ I₂ body proofOf)
    (preparedProof circuit₁ I₁ circuit₂ I₂ proofOf) dec₁ dec₂ rootOf₁ rootOf₂
    hfield₁ hfield₂ hmac hDigest hout₁ hout₂ hfront₁ hfront₂ tag hrowOne hrowTwo hspace
  convert! h using 1
  push_cast
  ring

/-- 117-bit work-normalized security with a finite additive offset. N
counts only the original prover's queries. -/
theorem extraction_117_of_ge (hN : 10 ≤ N) :
    probability (TM := TM) circuit₁ I₁ circuit₂ I₂ S₁ S₂ M geometry₁ geometry₂ sampling₁ sampling₂
      codec₁ codec₂ claimOf₁ claimOf₂ ht₁ ht₂ body proofOf dec₁ dec₂ rootOf₁ rootOf₂ ≤
      (2+N+tA : ℚ)/(2^117 : ℚ) := by
  rw [probability_eq_annotated]
  have h := RuntimeExtraction.extraction_117_of_ge circuit₁ I₁ circuit₂ I₂ S₁ S₂ M geometry₁ geometry₂ sampling₁ sampling₂
    codec₁ codec₂ (fun result : Out × C => claimOf₁ result.1) (fun result : Out × C => claimOf₂ result.1)
    ht₁ ht₂ (prepareBody circuit₁ I₁ circuit₂ I₂ body proofOf)
    (preparedProof circuit₁ I₁ circuit₂ I₂ proofOf) dec₁ dec₂ rootOf₁ rootOf₂
    hfield₁ hfield₂ hmac hDigest hout₁ hout₂ hfront₁ hfront₂ tag hrowOne hrowTwo hspace (by omega : 11 ≤ 1+N)
  convert! h using 1
  push_cast
  ring

/-- Unit-offset 117-bit extraction security for every pair of query budgets.
Small Merkle budgets require digest guessing; eight or more Merkle queries
pay for the finite startup cost in the existing composition bound. -/
theorem extraction_117 :
    probability (TM := TM) circuit₁ I₁ circuit₂ I₂ S₁ S₂ M geometry₁ geometry₂ sampling₁ sampling₂
      codec₁ codec₂ claimOf₁ claimOf₂ ht₁ ht₂ body proofOf dec₁ dec₂ rootOf₁ rootOf₂ ≤
      (1+N+tA : ℚ)/(2^117 : ℚ) := by
  by_cases hsmall : tA < 8
  · have h := probability_small_merkle circuit₁ I₁ circuit₂ I₂ S₁ S₂ M
      geometry₁ geometry₂ sampling₁ sampling₂ codec₁ codec₂ claimOf₁ claimOf₂ ht₁ ht₂
      body proofOf dec₁ dec₂ rootOf₁ rootOf₂ hsmall hspace
    have hfc : 2*I₂.n+2*I₁.n = 12992 := by rw [geometry₁.n,geometry₂.n]; rfl
    rw [hfc,hDigest,Nat.cast_pow,Nat.cast_ofNat] at h
    have hnum : 2*tA*tA+(12992+tA)*(2*tA+1) ≤ 195083 := by
      calc
        _ ≤ 2*7*7+(12992+7)*(2*7+1) := by gcongr <;> omega
        _ = _ := by norm_num
    have hprob : probability (TM := TM) circuit₁ I₁ circuit₂ I₂ S₁ S₂ M
        geometry₁ geometry₂ sampling₁ sampling₂ codec₁ codec₂ claimOf₁ claimOf₂ ht₁ ht₂
        body proofOf dec₁ dec₂ rootOf₁ rootOf₂ ≤ 1/(2^117 : ℚ) := by
      apply h.trans
      calc
        _ ≤ (195083 : ℚ)/2^256 := by gcongr; exact_mod_cast hnum
        _ ≤ _ := by norm_num
    apply hprob.trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg _
    have ht : (0 : ℚ) ≤ tA := Nat.cast_nonneg _
    linarith
  · exact RuntimeSecurity.tsec_117_of_merkle_ge
      (probability_le_one circuit₁ I₁ circuit₂ I₂ S₁ S₂ M geometry₁ geometry₂ sampling₁ sampling₂
        codec₁ codec₂ claimOf₁ claimOf₂ ht₁ ht₂ body proofOf dec₁ dec₂ rootOf₁ rootOf₂)
      (RuntimeSecurity.slots_le circuit₁ circuit₂ hfront₁ hfront₂) (by omega)
      (probability_bound circuit₁ I₁ circuit₂ I₂ S₁ S₂ M geometry₁ geometry₂ sampling₁ sampling₂
        codec₁ codec₂ claimOf₁ claimOf₂ ht₁ ht₂ body proofOf dec₁ dec₂ rootOf₁ rootOf₂
        hfield₁ hfield₂ hmac hDigest hout₁ hout₂ hfront₁ hfront₂ tag hrowOne hrowTwo hspace)

end LfzkV2.RawRuntimeExtraction
