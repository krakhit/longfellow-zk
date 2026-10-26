import LfzkV2.TwoFieldCommitmentFS
import Bcs.FixedPathCommit

/-! V1's fixed-path coupling for the actual V2 key-and-two-side schedule.
At zero transcript queries, fixing the Merkle tape fixes the proof and the
commitment context. All verifier answers then form a uniform independent tape. -/

namespace LfzkV2.TwoFieldCommitmentFS

open Finset RecursivePolygero Merkle.MH Merkle.RandomOracle TwoFieldReplay
open scoped Classical

variable {F₁ F₂ Key C Public Out Enc D : Type}
variable [Field F₁] [Fintype F₁] [DecidableEq F₁]
variable [Field F₂] [Fintype F₂] [DecidableEq F₂] [Fintype C] [Nonempty C]
variable [Fintype Key] [Fintype Public]
variable {out₁ input₁ out₂ input₂ tA TM fc : ℕ}
variable (circuit₁ : Circuit F₁ out₁ input₁) (I₁ : Instance F₁)
variable (circuit₂ : Circuit F₂ out₂ input₂) (I₂ : Instance F₂)
variable [Fintype (Replay.Payload circuit₁)] [Fintype (Replay.Payload circuit₂)]
variable [DecidableEq (Domain Key C Public circuit₁ I₁ circuit₂ I₂)]
variable [DecidableEq Enc] [Inhabited D] [DecidableEq Key]
variable (body : TwoOracleTree Enc D (Domain Key C Public circuit₁ I₁ circuit₂ I₂) C Out tA 0)
variable (proofOf : Out → Proof Key C Public circuit₁ I₁ circuit₂ I₂) (dflt : C)

/-- Exact equality of the complete zero-query verifier event with its
interactive tape experiment, including the physical Merkle oracle. -/
theorem zeroQuery_verifierEvent_ratio_eq
    (check : Out → Tree Enc D Unit fc) (mt : Fin TM → D)
    (dummy : Domain Key C Public circuit₁ I₁ circuit₂ I₂ → C)
    (E : (Key × List (Enc × D)) → (Enc → D) → Out →
      (Fin (1+(Replay.slots circuit₁+2)+(Replay.slots circuit₂+2)) → C) → Prop) :
    let K := setup circuit₁ I₁ circuit₂ I₂ body proofOf dflt
    ((univ.filter fun H : Domain Key C Public circuit₁ I₁ circuit₂ I₂ → C =>
        E (K.context mt H) (K.merkleOracle check mt H) (K.proof mt H) (K.challenges mt H)).card : ℚ)/
      (Fintype.card C : ℚ)^Fintype.card (Domain Key C Public circuit₁ I₁ circuit₂ I₂) =
    ((univ.filter fun tape : Fin (1+(Replay.slots circuit₁+2)+(Replay.slots circuit₂+2)) → C =>
        E (K.context mt dummy) (K.merkleOracle check mt dummy) (K.proof mt dummy) tape).card : ℚ)/
      (Fintype.card C : ℚ)^(1+(Replay.slots circuit₁+2)+(Replay.slots circuit₂+2)) :=
  (setup circuit₁ I₁ circuit₂ I₂ body proofOf dflt).zeroQuery_verifierEvent_ratio_eq
    check mt dummy (fun out => hashInput_injective circuit₁ I₁ circuit₂ I₂ (proofOf out)) E

/-- A fixed-Merkle-tape interactive bound transfers unchanged to V2's
zero-query random-oracle experiment. -/
theorem zeroQuery_verifierEvent_ratio_le [Fintype D]
    (check : Out → Tree Enc D Unit fc)
    (dummy : Domain Key C Public circuit₁ I₁ circuit₂ I₂ → C)
    (E : (Key × List (Enc × D)) → (Enc → D) → Out →
      (Fin (1+(Replay.slots circuit₁+2)+(Replay.slots circuit₂+2)) → C) → Prop)
    (epsilon : ℚ)
    (hinteractive : ∀ mt : Fin TM → D,
      let K := setup circuit₁ I₁ circuit₂ I₂ body proofOf dflt
      ((univ.filter fun tape : Fin (1+(Replay.slots circuit₁+2)+(Replay.slots circuit₂+2)) → C =>
          E (K.context mt dummy) (K.merkleOracle check mt dummy) (K.proof mt dummy) tape).card : ℚ)/
        (Fintype.card C : ℚ)^(1+(Replay.slots circuit₁+2)+(Replay.slots circuit₂+2)) ≤ epsilon) :
    let K := setup circuit₁ I₁ circuit₂ I₂ body proofOf dflt
    ((univ.filter fun ω : (Fin TM → D) × (Domain Key C Public circuit₁ I₁ circuit₂ I₂ → C) =>
        E (K.context ω.1 ω.2) (K.merkleOracle check ω.1 ω.2)
          (K.proof ω.1 ω.2) (K.challenges ω.1 ω.2)).card : ℚ)/
      ((Fintype.card D : ℚ)^TM *
        (Fintype.card C : ℚ)^Fintype.card (Domain Key C Public circuit₁ I₁ circuit₂ I₂)) ≤ epsilon := by
  have h := (setup circuit₁ I₁ circuit₂ I₂ body proofOf dflt).zeroQuery_verifierEvent_ratio_le
    check dummy (fun out => hashInput_injective circuit₁ I₁ circuit₂ I₂ (proofOf out)) E epsilon hinteractive
  simpa only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Nat.cast_mul, Nat.cast_pow] using h

end LfzkV2.TwoFieldCommitmentFS
