import Bcs.Compiled
import polygero.Protocol.Instance

/-! The concrete Polygero oracle is a family of physical columns, including
its additive proximity mask. V1's generic Merkle compiler applies through
this equivalence and the actual opening-only verifier. -/

namespace RecursivePolygero.MerkleCompiler

open LigeroFamily Local.Polygero Merkle Merkle.MH

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

abbrev Leaf (F : Type) (nw nq : ℕ) := Column F nw nq × F

def columnsEquiv (F : Type) (nw nq n : ℕ) : Oracle F nw nq n ≃ (Fin n → Leaf F nw nq) where
  toFun W j := (W.ordinary.column j,W.proximityMask j)
  invFun a :=
    ⟨⟨fun b i j => (a j).1.core b i,fun m j => (a j).1.checkedMask m⟩,fun j => (a j).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def compiler (I : Instance F) (ht : 0 < I.t) :
    Bcs.Compiler I.layer.Statement I.layer.Oracle I.layer.Coin I.layer.Payload I.layer.Query
      (Opening F I.nw I.nq I.n I.t) (Leaf F I.nw I.nq) I.n where
  protocol :=
    { language := fun σ => ∃ w, I.layer.satisfies σ w
      openOracle := openOracle
      verify := verify I.domain (by have := I.primary_le; omega) I.layout }
  columns := columnsEquiv F I.nw I.nq I.n
  indices query := query.coordinates
  indices_nonempty query := Finset.card_pos.mp (by simpa only [QuerySet.card_coordinates] using ht)
  open_congr first second query hagree := by
    apply Prod.ext
    · funext j
      exact congrArg Prod.fst (hagree j.val j.property)
    · funext j
      exact congrArg Prod.snd (hagree j.val j.property)

theorem verify_of_accepts (I : Instance F) (ht : 0 < I.t)
    {Salt D Enc : Type} [Inhabited D]
    (S : MH.Scheme Salt (Leaf F I.nw I.nq) D Enc)
    (σ : I.layer.Statement) (root : D) (coin : I.layer.Coin) (payload : I.layer.Payload)
    (query : I.layer.Query) (claim : OpeningClaim I.n Salt (Leaf F I.nw I.nq) D)
    (W : I.layer.Oracle)
    (hagree : ∀ j ∈ claim.I, columnsEquiv F I.nw I.nq I.n W j = claim.a j)
    (haccept : (compiler I ht).Accepts S σ root coin payload query claim) :
    I.layer.verify σ W coin payload query :=
  (compiler I ht).verify_of_accepts S σ root coin payload query claim W hagree haccept

noncomputable def extractedOracle (I : Instance F)
    {Salt D Enc : Type} [DecidableEq D] [Inhabited D] [Inhabited Salt] [Inhabited (Leaf F I.nw I.nq)]
    {codec : Codec Salt (Leaf F I.nw I.nq) D Enc} (dec : RoleDecoders codec)
    (root : D) (trace : List (Enc × D)) : I.layer.Oracle :=
  (columnsEquiv F I.nw I.nq I.n).symm
    (((extract dec I.n root trace).map Extracted.message).getD default)

/-- Explaining the opened leaves suffices to replace the claimed oracle by
the cut-trace oracle in the actual Polygero verifier. -/
theorem verify_of_extraction (I : Instance F) (ht : 0 < I.t)
    {Salt D Enc : Type} [DecidableEq D] [Inhabited D] [Inhabited Salt]
    [Inhabited (Leaf F I.nw I.nq)]
    {codec : Codec Salt (Leaf F I.nw I.nq) D Enc} (dec : RoleDecoders codec)
    (S : MH.Scheme Salt (Leaf F I.nw I.nq) D Enc)
    (σ : I.layer.Statement) (root : D) (trace : List (Enc × D))
    (coin : I.layer.Coin) (payload : I.layer.Payload) (query : I.layer.Query)
    (claim : OpeningClaim I.n Salt (Leaf F I.nw I.nq) D)
    (e : Extracted I.n Salt (Leaf F I.nw I.nq) D)
    (hext : extract dec I.n root trace = some e)
    (hagree : ∀ j ∈ claim.I, e.message j = claim.a j)
    (haccept : (compiler I ht).Accepts S σ root coin payload query claim) :
    I.layer.verify σ (extractedOracle I dec root trace) coin payload query := by
  apply verify_of_accepts I ht S σ root coin payload query claim _ _ haccept
  intro j hj
  simpa only [extractedOracle, Equiv.apply_symm_apply, hext, Option.map_some, Option.getD_some] using hagree j hj

end RecursivePolygero.MerkleCompiler
