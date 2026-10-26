import LfzkV2.GradedFS
import polygero.FiatShamir.MerkleCompiler

/-! A compiled V2 side for V1's extraction-first two-field blueprint.
Public inputs may depend on the claimed MAC answer and public data carried
by the hash point; the committed witness list is fixed by its oracle. -/

namespace LfzkV2

open SumcheckV2 RecursivePolygero NonrecursiveFS ConcreteFS Finset Bcs.TotalOracle
open scoped Classical

variable {F C Context : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype C]
variable {out input : ℕ}

structure CompiledSide (F C Context : Type) [Field F] [Fintype F] [DecidableEq F] [Fintype C]
    {out input : ℕ} (circuit : Circuit F out input) (I : Instance F) where
  Pad : Type
  Slot : Type
  plan : Replay.PadPlan (Pad := Pad) (Slot := Slot) circuit
  sampling : Replay.Sampling F C circuit
  dflt : C
  nPublic : ℕ
  nPrivate : ℕ
  index : (Fin nPublic ⊕ Fin nPrivate) ↪ Cube input
  publicInputs : Context → Fin nPublic → F
  privateCoordinate : Fin nPrivate → Slot
  coordinate : Pad → Slot
  primary : Slot → Fin I.nw × Fin I.q
  product : (v : Reconstruction circuit Pad Slot) →
    Fin v.constraints.layers.length → Fin I.nq × Fin I.q
  eqns : ∀ ctx (v : Reconstruction circuit Pad Slot), I.Equations ≃ Backend.Equation
    (v.rows index (publicInputs ctx) privateCoordinate coordinate).length v.constraints.layers.length
  cutoff : ℕ
  bound : ℕ
  cutoff_gt : I.r+I.w-1 < cutoff
  packing : CodingTheory.UniformFamilyBound I.n cutoff (I.r+I.w-1) bound
  decodeCoin : C → I.layer.Coin
  decodeQuery : C → I.layer.Query
  potential : TerminalPotential I cutoff decodeCoin decodeQuery

namespace CompiledSide

variable {circuit : Circuit F out input} {I : Instance F}
variable (S : CompiledSide F C Context circuit I)

noncomputable def value (g : (Counting.tupleCounts I).Index) : S.Slot → F :=
  Backend.read ((Counting.tupleCounts I).witness g) ∘ Backend.linearAddress S.primary

noncomputable def inputOf (ctx : Context) (g : (Counting.tupleCounts I).Index) : Cube input → F :=
  circuitInputs S.index (S.publicInputs ctx) S.privateCoordinate (S.value g)

noncomputable def statement (ctx : Context) (v : Reconstruction circuit S.Pad S.Slot) : I.layer.Statement :=
  v.backendStatement S.index (S.publicInputs ctx) S.privateCoordinate S.coordinate I S.primary
    (S.product v) (S.eqns ctx v)

noncomputable def candidateInput (ctx : Context) (W : I.layer.Oracle) (candidate : Fin S.bound) : Cube input → F :=
  S.inputOf ctx (Counting.committedCandidate I W S.cutoff S.bound candidate)

noncomputable def candidatePads (W : I.layer.Oracle) (candidate : Fin S.bound) : S.Pad → F :=
  S.value (Counting.committedCandidate I W S.cutoff S.bound candidate) ∘ S.coordinate

def Good (ctx : Context) (W : I.layer.Oracle) (g : (Counting.tupleCounts I).Index) : Prop :=
  g ∈ Counting.committedCandidates I W S.cutoff ∧ circuit.Satisfies (S.inputOf ctx g)

variable {Parent : Type} (keyOf : Parent → Context) (payloadOf : Parent → Replay.Payload circuit)

noncomputable def charge (W : I.layer.Oracle) (x : Domain Context circuit I Parent)
    (pref : Fin ((GradedReplay.points circuit I keyOf payloadOf).slot x) → C) (c : C) : ℚ :=
  let ctx := Replay.queryKey circuit (roleKey I keyOf) x
  GradedFS.charge circuit I S.plan S.sampling S.dflt keyOf payloadOf
    (S.statement ctx) (S.candidateInput ctx) S.candidatePads S.potential W x pref c

theorem charge_nonneg (W : I.layer.Oracle) (x : Domain Context circuit I Parent)
    (pref : Fin ((GradedReplay.points circuit I keyOf payloadOf).slot x) → C) (c : C) :
    0 ≤ S.charge keyOf payloadOf W x pref c :=
  GradedFS.charge_nonneg circuit I S.plan S.sampling S.dflt keyOf payloadOf
    (S.statement _) (S.candidateInput _) S.candidatePads S.potential W x pref c

theorem charge_sum_le (W : I.layer.Oracle) (x : Domain Context circuit I Parent)
    (pref : Fin ((GradedReplay.points circuit I keyOf payloadOf).slot x) → C) :
    (∑ c : C, S.charge keyOf payloadOf W x pref c) ≤
      GradedFS.budget (bound := S.bound) circuit I S.sampling S.potential x :=
  GradedFS.charge_sum_le circuit I S.plan S.sampling S.dflt keyOf payloadOf
    (S.statement _) (S.candidateInput _) S.candidatePads S.potential W x pref

noncomputable def Accepts (W : I.layer.Oracle) (H : Domain Context circuit I Parent → C)
    (selected : Parent × I.layer.Payload) : Prop :=
  I.layer.verify
    (S.statement (keyOf selected.1)
      (Replay.reconstruction S.sampling.decode circuit S.plan (keyOf selected.1) (payloadOf selected.1) H)) W
    (S.decodeCoin (H (ConcreteFS.parent circuit I selected.1))) selected.2
    (S.decodeQuery (H (ConcreteFS.child circuit I selected.1 selected.2)))

/-- The same verifier with authenticated columns, before replacing its
openings by the common cut-trace oracle. -/
noncomputable def CompiledAccepts {Salt D Enc : Type} [Inhabited D] (ht : 0 < I.t)
    (scheme : Merkle.MH.Scheme Salt (MerkleCompiler.Leaf F I.nw I.nq) D Enc)
    (H : Domain Context circuit I Parent → C) (selected : Parent × I.layer.Payload) (root : D)
    (claim : Merkle.MH.OpeningClaim I.n Salt (MerkleCompiler.Leaf F I.nw I.nq) D) : Prop :=
  (MerkleCompiler.compiler I ht).Accepts scheme
    (S.statement (keyOf selected.1)
      (Replay.reconstruction S.sampling.decode circuit S.plan (keyOf selected.1) (payloadOf selected.1) H)) root
    (S.decodeCoin (H (ConcreteFS.parent circuit I selected.1))) selected.2
    (S.decodeQuery (H (ConcreteFS.child circuit I selected.1 selected.2))) claim

theorem accepts_of_extraction {Salt D Enc : Type} [DecidableEq D] [Inhabited D] [Inhabited Salt]
    [Inhabited (MerkleCompiler.Leaf F I.nw I.nq)]
    (ht : 0 < I.t) {codec : Merkle.MH.Codec Salt (MerkleCompiler.Leaf F I.nw I.nq) D Enc}
    (dec : Merkle.MH.RoleDecoders codec)
    (scheme : Merkle.MH.Scheme Salt (MerkleCompiler.Leaf F I.nw I.nq) D Enc)
    (H : Domain Context circuit I Parent → C) (selected : Parent × I.layer.Payload) (root : D)
    (trace : List (Enc × D))
    (claim : Merkle.MH.OpeningClaim I.n Salt (MerkleCompiler.Leaf F I.nw I.nq) D)
    (e : Merkle.MH.Extracted I.n Salt (MerkleCompiler.Leaf F I.nw I.nq) D)
    (hext : Merkle.MH.extract dec I.n root trace = some e)
    (hagree : ∀ j ∈ claim.I, e.message j = claim.a j)
    (haccept : S.CompiledAccepts keyOf payloadOf ht scheme H selected root claim) :
    S.Accepts keyOf payloadOf (MerkleCompiler.extractedOracle I dec root trace) H selected :=
  MerkleCompiler.verify_of_extraction I ht dec scheme _ root trace _ selected.2 _ claim e hext hagree haccept

/-- A side without a satisfying committed candidate pays a unit on its
actual path, uniformly in the public inputs carried by that path. -/
theorem path_charge_ge_one (W : I.layer.Oracle) (H : Domain Context circuit I Parent → C)
    (selected : Parent × I.layer.Payload)
    (hbad : ¬ ∃ g, S.Good (keyOf selected.1) W g)
    (haccept : S.Accepts keyOf payloadOf W H selected) :
    1 ≤ ∑ i : Fin (Replay.slots circuit+2), S.charge keyOf payloadOf W
      (GradedReplay.hashInput circuit I keyOf payloadOf selected i.val)
      ((GradedReplay.points circuit I keyOf payloadOf).chal H
        (GradedReplay.hashInput circuit I keyOf payloadOf selected i.val))
      (H (GradedReplay.hashInput circuit I keyOf payloadOf selected i.val)) := by
  have hp := GradedFS.path_charge_ge_one circuit I S.plan S.sampling S.dflt keyOf payloadOf
    (S.statement (keyOf selected.1)) (S.candidateInput (keyOf selected.1)) S.candidatePads S.potential
    W H selected (Counting.committedCandidates_card_le I W S.cutoff S.bound S.cutoff_gt S.packing)
    (by
      intro candidate hmem hsat
      exact hbad ⟨_,hmem,hsat⟩)
    (by
      intro candidate hsat
      apply Replay.reconstruction_accepts S.sampling.decode circuit S.plan (keyOf selected.1) (payloadOf selected.1)
        H S.index (S.publicInputs (keyOf selected.1)) S.privateCoordinate S.coordinate _
      exact (Replay.reconstruction S.sampling.decode circuit S.plan (keyOf selected.1) (payloadOf selected.1) H).satisfies_accepts
        S.index (S.publicInputs (keyOf selected.1)) S.privateCoordinate S.coordinate I S.primary _ _ _ hsat)
    haccept
  refine hp.trans_eq ?_
  apply sum_congr rfl
  intro i _
  dsimp only [charge]
  rw [GradedReplay.hashInput_key]

end CompiledSide
end LfzkV2
