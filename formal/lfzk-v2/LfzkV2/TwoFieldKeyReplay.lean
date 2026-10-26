import LfzkV2.TwoFieldReplay
import Bcs.VerifierQuery
import Merkle.TwoOracle

/-! Rust carries the tags and the two side proofs; the verifier recomputes
the MAC multiplier after reading both commitments. Annotating that raw proof
with the recomputed answer connects it to the fixed-input transcript model. -/

namespace LfzkV2.TwoFieldReplay

open RecursivePolygero Bcs.TotalOracle Merkle.RandomOracle

variable {F₁ F₂ Key C Public Out Enc D : Type}
variable [Field F₁] [Fintype F₁] [DecidableEq F₁]
variable [Field F₂] [Fintype F₂] [DecidableEq F₂]
variable {out₁ input₁ out₂ input₂ N tA TM : ℕ}
variable (circuit₁ : Circuit F₁ out₁ input₁) (I₁ : Instance F₁)
variable (circuit₂ : Circuit F₂ out₂ input₂) (I₂ : Instance F₂)

abbrev RawProof := Proof Key Unit Public circuit₁ I₁ circuit₂ I₂

def annotate (raw : RawProof (Key := Key) (Public := Public) circuit₁ I₁ circuit₂ I₂) (answer : C) :
    Proof Key C Public circuit₁ I₁ circuit₂ I₂ where
  context := (raw.context.1,answer,raw.context.2.2)
  payloadOne := raw.payloadOne
  responseOne := raw.responseOne
  payloadTwo := raw.payloadTwo
  responseTwo := raw.responseTwo

def rawKey (raw : RawProof (Key := Key) (Public := Public) circuit₁ I₁ circuit₂ I₂) : Key := raw.context.1

def preparedProof (proofOf : Out → RawProof (Key := Key) (Public := Public) circuit₁ I₁ circuit₂ I₂)
    (result : Out × C) : Proof Key C Public circuit₁ I₁ circuit₂ I₂ :=
  annotate circuit₁ I₁ circuit₂ I₂ (proofOf result.1) result.2

theorem preparedProof_key_input
    (proofOf : Out → RawProof (Key := Key) (Public := Public) circuit₁ I₁ circuit₂ I₂) (out : Out) (c : C) :
    hashInput circuit₁ I₁ circuit₂ I₂ (preparedProof circuit₁ I₁ circuit₂ I₂ proofOf (out,c)) 0 =
      .inl (rawKey circuit₁ I₁ circuit₂ I₂ (proofOf out)) := rfl

def prepareBody (body : TwoOracleTree Enc D (Domain Key C Public circuit₁ I₁ circuit₂ I₂) C Out tA N)
    (proofOf : Out → RawProof (Key := Key) (Public := Public) circuit₁ I₁ circuit₂ I₂) :
    TwoOracleTree Enc D (Domain Key C Public circuit₁ I₁ circuit₂ I₂) C (Out × C) tA (1+N) :=
  body.bindRight fun out => Tree.query (.inl (rawKey circuit₁ I₁ circuit₂ I₂ (proofOf out)))
    (fun c => Tree.done (out,c))

theorem prepareBody_fixLeft [DecidableEq Enc]
    (body : TwoOracleTree Enc D (Domain Key C Public circuit₁ I₁ circuit₂ I₂) C Out tA N)
    (proofOf : Out → RawProof (Key := Key) (Public := Public) circuit₁ I₁ circuit₂ I₂)
    (mt : Fin TM → D) (dflt : D) (seen : List Enc) :
    TwoOracleTree.fixLeft mt dflt (prepareBody circuit₁ I₁ circuit₂ I₂ body proofOf) seen =
      VerifierQuery.prepare (TwoOracleTree.fixLeft mt dflt body seen)
        (fun out => .inl (rawKey circuit₁ I₁ circuit₂ I₂ (proofOf out))) := by
  rw [prepareBody,TwoOracleTree.fixLeft_bindRight]
  rfl

/-- Key coherence follows from replay, including when the original prover
never queried the key. It is not an additional check on serialized bytes. -/
theorem preparedProof_coherent
    (tree : Tree (Domain Key C Public circuit₁ I₁ circuit₂ I₂) C Out N)
    (proofOf : Out → RawProof (Key := Key) (Public := Public) circuit₁ I₁ circuit₂ I₂)
    (H : Domain Key C Public circuit₁ I₁ circuit₂ I₂ → C) :
    let result := ((VerifierQuery.prepare tree
      (fun out => .inl (rawKey circuit₁ I₁ circuit₂ I₂ (proofOf out)))).run H).1
    let proof := preparedProof circuit₁ I₁ circuit₂ I₂ proofOf result
    proof.context.2.1 = H (.inl proof.context.1) := by
  rw [VerifierQuery.prepare_output]
  rfl

end LfzkV2.TwoFieldReplay
