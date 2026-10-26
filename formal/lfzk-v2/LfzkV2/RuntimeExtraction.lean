import LfzkV2.AuthenticatedProbability
import LfzkV2.RuntimeSecurity

/-! Numerical extraction endpoints for the annotated authenticated V2
proof model. Circuit/MAC correspondence and balanced samplers are explicit
parameters. The unit-offset 117-bit endpoint retains N ≥ 11.
RawRuntimeExtraction combines these bounds with a small-query Merkle argument
to give raw proofs a unit-offset 117-bit bound for all budgets, including a
conservative verifier-lookup charge. -/

namespace LfzkV2.RuntimeExtraction

open Finset RecursivePolygero Merkle Merkle.MH Merkle.RandomOracle TwoFieldReplay RuntimeProfiles
open scoped Classical

variable {F₁ F₂ Key C Public Out Enc D Salt₁ Salt₂ Fmac : Type}
variable [Field F₁] [Fintype F₁] [DecidableEq F₁]
variable [Field F₂] [Fintype F₂] [DecidableEq F₂]
variable [Fintype C] [Fintype Key] [Fintype Public] [Fintype D]
variable [DecidableEq Key] [DecidableEq D] [DecidableEq Enc] [Inhabited D]
variable [Field Fmac] [Fintype Fmac] [DecidableEq Fmac]
variable {out₁ input₁ out₂ input₂ blocks tA N TM : ℕ}
variable (circuit₁ : Circuit F₁ out₁ input₁) (I₁ : Instance F₁)
variable (circuit₂ : Circuit F₂ out₂ input₂) (I₂ : Instance F₂)
variable [Inhabited Salt₁] [Inhabited Salt₂]
variable [Inhabited (MerkleCompiler.Leaf F₁ I₁.nw I₁.nq)]
variable [Inhabited (MerkleCompiler.Leaf F₂ I₂.nw I₂.nq)]
variable [Fintype (Replay.Payload circuit₁)] [Fintype (Replay.Payload circuit₂)]
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
variable (proofOf : Out → Proof Key C Public circuit₁ I₁ circuit₂ I₂)
variable (dec₁ : RoleDecoders codec₁) (dec₂ : RoleDecoders codec₂) (rootOf₁ rootOf₂ : Key → D)

noncomputable def probability : ℚ :=
  TwoFieldCommitmentFS.failureProbability (TM := TM) circuit₁ I₁ circuit₂ I₂
    (S₁.withProfile Hash.profile geometry₁ sampling₁) (S₂.withProfile Signature.profile geometry₂ sampling₂)
    M codec₁ codec₂ claimOf₁ claimOf₂ ht₁ ht₂ body proofOf dec₁ dec₂ rootOf₁ rootOf₂

theorem probability_le_one :
    probability (TM := TM) circuit₁ I₁ circuit₂ I₂ S₁ S₂ M geometry₁ geometry₂ sampling₁ sampling₂
      codec₁ codec₂ claimOf₁ claimOf₂ ht₁ ht₂ body proofOf dec₁ dec₂ rootOf₁ rootOf₂ ≤ 1 :=
  TwoFieldCommitmentFS.failureProbability_le_one (TM := TM) circuit₁ I₁ circuit₂ I₂
    (S₁.withProfile Hash.profile geometry₁ sampling₁) (S₂.withProfile Signature.profile geometry₂ sampling₂)
    M codec₁ codec₂ claimOf₁ claimOf₂ ht₁ ht₂ body proofOf dec₁ dec₂ rootOf₁ rootOf₂

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

theorem probability_bound :
    probability (TM := TM) circuit₁ I₁ circuit₂ I₂ S₁ S₂ M geometry₁ geometry₂ sampling₁ sampling₂
      codec₁ codec₂ claimOf₁ claimOf₂ ht₁ ht₂ body proofOf dec₁ dec₂ rootOf₁ rootOf₂ ≤
      N*RuntimeCost.coefficient+RuntimeCost.constant+
        2*(Bcs.AdaptiveCommit.adaptiveNumerator 12992 tA
          (1+(Replay.slots circuit₁+2)+(Replay.slots circuit₂+2)+N) : ℚ)/(2^256 : ℚ) := by
  letI : Nonempty C := ⟨S₁.dflt⟩
  have hp := TwoFieldCommitmentFS.failureProbability_le (TM := TM) circuit₁ I₁ circuit₂ I₂
    (S₁.withProfile Hash.profile geometry₁ sampling₁) (S₂.withProfile Signature.profile geometry₂ sampling₂)
    M codec₁ codec₂ claimOf₁ claimOf₂ ht₁ ht₂ body proofOf dec₁ dec₂ rootOf₁ rootOf₂ tag hrowOne hrowTwo hspace
  let proof := proofOf ((TwoFieldCommitmentFS.setup circuit₁ I₁ circuit₂ I₂ body proofOf S₁.dflt).proof
    (fun _ : Fin TM => default) (fun _ => S₁.dflt))
  have hcost := RuntimeCost.error_le circuit₁ I₁ circuit₂ I₂ S₁ S₂ geometry₁ geometry₂ sampling₁ sampling₂
    hfield₁ hfield₂ hmac hout₁ hout₂ hfront₁ hfront₂ M N proof
  apply hp.trans (add_le_add hcost ?_)
  have hfc : 2*I₂.n+2*I₁.n = 12992 := by rw [geometry₁.n,geometry₂.n]; rfl
  rw [hfc,hDigest,Nat.cast_pow,Nat.cast_ofNat]

/-- Conservative extraction bound for the annotated authenticated two-field
model, including the affine MAC and both Merkle explanations. -/
theorem extraction_114 :
    probability (TM := TM) circuit₁ I₁ circuit₂ I₂ S₁ S₂ M geometry₁ geometry₂ sampling₁ sampling₂
      codec₁ codec₂ claimOf₁ claimOf₂ ht₁ ht₂ body proofOf dec₁ dec₂ rootOf₁ rootOf₂ ≤
      (1+N+tA : ℚ)/(2^114 : ℚ) := by
  have hp := probability_bound circuit₁ I₁ circuit₂ I₂ S₁ S₂ M geometry₁ geometry₂ sampling₁ sampling₂
    codec₁ codec₂ claimOf₁ claimOf₂ ht₁ ht₂ body proofOf dec₁ dec₂ rootOf₁ rootOf₂
    hfield₁ hfield₂ hmac hDigest hout₁ hout₂ hfront₁ hfront₂ tag hrowOne hrowTwo hspace
  exact RuntimeSecurity.tsec_114 (probability_le_one circuit₁ I₁ circuit₂ I₂ S₁ S₂ M geometry₁ geometry₂ sampling₁ sampling₂
    codec₁ codec₂ claimOf₁ claimOf₂ ht₁ ht₂ body proofOf dec₁ dec₂ rootOf₁ rootOf₂)
    (RuntimeSecurity.slots_le circuit₁ circuit₂ hfront₁ hfront₂) hp

/-- The direct numerical comparison uses at least 11 transcript queries.
RawRuntimeExtraction supplies the all-budget endpoint using Merkle acceptance. -/
theorem extraction_117_of_ge (hN : 11 ≤ N) :
    probability (TM := TM) circuit₁ I₁ circuit₂ I₂ S₁ S₂ M geometry₁ geometry₂ sampling₁ sampling₂
      codec₁ codec₂ claimOf₁ claimOf₂ ht₁ ht₂ body proofOf dec₁ dec₂ rootOf₁ rootOf₂ ≤
      (1+N+tA : ℚ)/(2^117 : ℚ) := by
  have hp := probability_bound circuit₁ I₁ circuit₂ I₂ S₁ S₂ M geometry₁ geometry₂ sampling₁ sampling₂
    codec₁ codec₂ claimOf₁ claimOf₂ ht₁ ht₂ body proofOf dec₁ dec₂ rootOf₁ rootOf₂
    hfield₁ hfield₂ hmac hDigest hout₁ hout₂ hfront₁ hfront₂ tag hrowOne hrowTwo hspace
  exact RuntimeSecurity.tsec_117_of_ge
    (probability_le_one circuit₁ I₁ circuit₂ I₂ S₁ S₂ M geometry₁ geometry₂ sampling₁ sampling₂
      codec₁ codec₂ claimOf₁ claimOf₂ ht₁ ht₂ body proofOf dec₁ dec₂ rootOf₁ rootOf₂)
    (RuntimeSecurity.slots_le circuit₁ circuit₂ hfront₁ hfront₂) hN hp

end LfzkV2.RuntimeExtraction
