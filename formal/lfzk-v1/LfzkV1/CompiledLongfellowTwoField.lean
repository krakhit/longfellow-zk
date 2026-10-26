import LfzkV1.CompiledLongfellow
import LfzkV1.NizkGrindingTwoField

/-!
# Two-field Longfellow at the compiled verifier

`LfzkV1.NizkGrindingTwoField.FSFamily` is one grinding Fiat–Shamir side of a two-field argument, over an
abstract compiled verifier `K` with abstract `challengeOf`, `queryOf`, `statement`, `lig` and the
acceptance bridge `hright`.  `CompiledFSFamily` is the same side at the compiled Longfellow verifier
of `LfzkV1.CompiledLongfellow`: `K` is `guarded (v1K …)`, the challenge and query are the decoded
recomputed Ligero rounds, the Ligero instance is the Merkle-extracted one, and `hright` is the
theorem `CompiledLongfellow.hright_v1`.  `toFSFamily` builds the `FSFamily`, so the two-field
composition applies verbatim.

The side's verifier code `V` and proof parsing `msgOf` are parameters of the family, fixed across
the absorbed coordinate `z`; its Ligero statement `stmt z` may read `z`, because a two-field side's
statement carries the MAC key, which is a coin of the merged tape.

`toMacBound_accepts_iff` says the event's side acceptances are
the compiled verifiers on the merged tape.  What remains a hypothesis is listed there.  Which
verifier `Accepts` is (the non-ZK-path sumcheck checks with a commitment-fixed Ligero statement, not
the deployed zero-knowledge verifier), and the residual refinement claim, are in
`LfzkV1.CompiledLongfellow`'s module docstring; they apply to each side.  Not imported by `LfzkV1.lean`,
as `LfzkV1.NizkGrindingTwoField` is not.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LfzkV1.CompiledLongfellowTwoField

open Finset Bcs Merkle Merkle.MH Merkle.RandomOracle
open scoped Classical
open LfzkV1.Mac LfzkV1.TwoField LfzkV1.TwoFieldNizk LfzkV1.TwoFieldBridge LfzkV1.CertifiedV1
open LfzkV1.NizkGrinding LfzkV1.TwoFieldV1Rows LfzkV1.NizkGrindingTwoField LfzkV1.CompiledLongfellow

/--
**One grinding Fiat–Shamir side at the compiled Longfellow verifier.**

`FSFamily` without `challengeOf`, `queryOf`, `statement`, `lig` and `hright`, with the Ligero
statement `stmt` and the matching premise `hmatch` in their place.  The verifier is
`Accepts (v1K …) V … msgOf (stmt z)`, at the code `V`, the parsing `msgOf` and the domain `dom`.
-/
structure CompiledFSFamily (R : Row) (hR : R.Valid) (hr : 0 < R.params.row.openings)
    (Z : Type) (C : Type) [Fintype C] [DecidableEq C]
    (Cand F Equations Witness : Type) [Fintype Cand] [Field F] [Fintype F] [DecidableEq F]
    [SumcheckV1Interp F] [Fintype Equations] [DecidableEq Equations]
    (nc nv logw logc : ℕ)
    {Enc D Salt : Type} [Fintype D] [Inhabited D] [DecidableEq D] [DecidableEq Enc]
    [Inhabited Salt]
    (Ctx Msg Out : Type) [DecidableEq Ctx] [DecidableEq Msg] [Inhabited Msg] (N : ℕ)
    (Aux Aux' : Type) (tlen respondFuel revealFuel : ℕ)
    {codec : Codec Salt (Col F R.params.nw R.params.nq) D Enc} (dec : RoleDecoders codec)
    (dom : LigeroFamily.ReedSolomon.Domain F R.params.row.openings R.params.q R.params.row.n)
    (V : Code C F (LigeroV1LayerStep.Chal F Equations R.params.nw R.params.nq)
      (LigeroV1LayerStep.Qry R.params.row) Msg logw logc)
    (msgOf : Out → ℕ → Msg) where
  /-- The side's Merkle adversary, at each value of the coordinates it does not read. -/
  A : Z → Adversary Enc D Salt (Col F R.params.nw R.params.nq)
    (LigeroV1LayerStep.Chal F Equations R.params.nw R.params.nq)
    (LigeroFamily.Response F R.params.row.openings R.params.q R.params.row.n 1)
    (LigeroV1LayerStep.Qry R.params.row) Aux Aux' R.params.row.n R.commitFuel respondFuel revealFuel
  /-- The side's Fiat–Shamir search, run after the commitment. -/
  adv : Z → Aux → Tree (Point Ctx Msg C R.params.nl R.params.rounds) C Out N
  /-- The answer an out-of-range slot would give; never read. -/
  dflt : C
  /-- The hash inputs' commitment context. -/
  ctxOf : Z → Aux → Ctx
  /-- The side's Ligero statement — in a two-field argument it includes the MAC key and tag. -/
  stmt : Z → (Fin tlen → D) →
    LigeroFamily.ConstraintSystem F R.params.nw R.params.nq R.params.q Equations
  /-- LayerStep's honest values, per commitment. -/
  H : Z → (Fin tlen → D) → RbrLongfellow.Honest F Cand logw logc
  /-- Which candidates satisfy the side's circuit, per commitment. -/
  Sat : Z → (Fin tlen → D) → Cand → Prop
  /-- The field half of LayerStep, per commitment. -/
  field : ∀ (z : Z) (pre : Fin tlen → D),
    RbrSplit.FieldData C F (LigeroV1LayerStep.Chal F Equations R.params.nw R.params.nq)
      (LigeroV1LayerStep.Qry R.params.row) Cand Witness nc nv logw logc (H z pre) (Sat z pre)
  /-- Its decoders are exactly balanced. -/
  hexact : ∀ (z : Z) (pre : Fin tlen → D), (field z pre).Exact
  /-- How a round's message fixes LayerStep's prover data at that round. -/
  MD : ∀ (z : Z) (pre : Fin tlen → D), MsgData C Msg (H z pre)
  /-- **LayerStep data describes the verifier** (`CompiledLongfellow.Matches`). -/
  hmatch : ∀ (z : Z) (pre : Fin tlen → D), Matches V (field z pre) (MD z pre)
  /-- **Ligero's extractor**: no satisfying candidate means a false Ligero statement. -/
  hfalse : ∀ (z : Z) (pre : Fin tlen → D), (∀ cand : Cand, ¬ Sat z pre cand) →
    ¬ (stmt z pre).Language
  /-- The side's row and the shared hash tape agree on its length. -/
  htape : R.tape = tlen
  hF : Fintype.card F = R.params.row.fieldSize
  hcand : Fintype.card Cand = R.cardCand
  hD : Fintype.card D = 2 ^ R.params.digestBits
  /-- The Merkle extractor's fuels. -/
  ht₁ : R.commitFuel ≤ tlen
  hT : 2 * R.params.row.n + (revealFuel + respondFuel) + R.commitFuel ≤ tlen
  hT1 : 1 ≤ tlen

namespace CompiledFSFamily

variable {R : Row} {hR : R.Valid} {hr : 0 < R.params.row.openings} {Z : Type} {C : Type}
  [Fintype C] [DecidableEq C] [Nonempty C]
variable {Cand F Equations Witness : Type} [Fintype Cand] [Nonempty Cand] [Field F] [Fintype F]
  [DecidableEq F] [SumcheckV1Interp F] [Fintype Equations] [DecidableEq Equations]
variable {nc nv logw logc : ℕ}
variable {Enc D Salt : Type} [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc]
  [Inhabited Salt]
variable {Ctx Msg Out : Type} [DecidableEq Ctx] [DecidableEq Msg] [Inhabited Msg] {N : ℕ}
variable {Aux Aux' : Type} {tlen respondFuel revealFuel : ℕ}
variable {codec : Codec Salt (Col F R.params.nw R.params.nq) D Enc} {dec : RoleDecoders codec}
variable {dom : LigeroFamily.ReedSolomon.Domain F R.params.row.openings R.params.q R.params.row.n}
variable {V : Code C F (LigeroV1LayerStep.Chal F Equations R.params.nw R.params.nq)
  (LigeroV1LayerStep.Qry R.params.row) Msg logw logc} {msgOf : Out → ℕ → Msg}
variable (L : CompiledFSFamily R hR hr Z C Cand F Equations Witness nc nv logw logc Ctx Msg Out N
  Aux Aux' tlen respondFuel revealFuel dec dom V msgOf)

/-- The side's compiled verifier at absorbed coordinate `z`. -/
def accepts (z : Z) (x : (Fin tlen → D) × (Fin (R.fsLen N) → C)) : Prop :=
  Accepts (v1K (Row.rowValid hR) dom (Row.hkrow hR) hr) V (L.A z) codec (L.adv z) L.dflt (L.ctxOf z)
    msgOf (L.stmt z) x

/-- **The `FSFamily` the compiled side is.**  `K := guarded (v1K …)`; `challengeOf`, `queryOf`,
`statement` and `lig` are `CompiledLongfellow`'s; `hright` is `hright_v1`. -/
noncomputable def toFSFamily :
    FSFamily (Enc := Enc) (D := D) (Salt := Salt) (M := Col F R.params.nw R.params.nq)
      R hR Z C Cand F Equations Witness nc nv logw logc Ctx Msg Out N Aux Aux' tlen
      R.params.row.n respondFuel revealFuel dec
      (guarded (v1K (Equations := Equations) (nw := R.params.nw) (nq := R.params.nq)
        (Row.rowValid hR) dom (Row.hkrow hR) hr)) dom where
  A := L.A
  adv := L.adv
  dflt := L.dflt
  ctxOf := L.ctxOf
  msgOf _ := msgOf
  challengeOf z := challengeOf V (L.adv z) L.dflt (L.ctxOf z) msgOf
  queryOf z := queryOf V (L.adv z) L.dflt (L.ctxOf z) msgOf
  statement z := guardedStatement V (L.A z) (L.adv z) L.dflt (L.ctxOf z) msgOf (L.stmt z)
  lig z := extractedInstance (Row.rowValid hR) dom (Row.hkrow hR) hr dec (L.A z) (L.stmt z)
  H := L.H
  Sat := L.Sat
  field := L.field
  hexact := L.hexact
  MD := L.MD
  hfalse := L.hfalse
  hright z pre _ ct := hright_v1 (Row.rowValid hR) dom (Row.hkrow hR) hr dec V (L.A z) (L.adv z)
    L.dflt (L.ctxOf z) msgOf (L.stmt z) (L.field z pre) (L.MD z pre) (L.hmatch z pre) pre ct
  htape := L.htape
  hF := L.hF
  hcand := L.hcand
  hD := L.hD
  ht₁ := L.ht₁
  hT := L.hT
  hT1 := L.hT1

omit [Nonempty C] [Nonempty Cand] in
/-- **The built family's verifier is the compiled verifier.** -/
theorem toFSFamily_accepts_iff (z : Z) (x : (Fin tlen → D) × (Fin (R.fsLen N) → C)) :
    L.toFSFamily.accepts z x ↔ L.accepts z x :=
  (accepts_iff_guarded _ V (L.A z) codec (L.adv z) L.dflt (L.ctxOf z) msgOf (L.stmt z) x).symm

end CompiledFSFamily

/-! ## Acceptance on the merged tape -/

section Headline

variable {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {D : Type} [Fintype D] [DecidableEq D] [Inhabited D]
variable {Fmac : Type} [Field Fmac] [Fintype Fmac] {nblk tlen : ℕ} {N₁ N₂ : ℕ}
variable {Cand₁ F₁ Equations₁ Witness₁ : Type} [Fintype Cand₁] [Nonempty Cand₁] [Field F₁]
  [Fintype F₁] [DecidableEq F₁] [SumcheckV1Interp F₁] [Fintype Equations₁] [DecidableEq Equations₁]
variable {nc₁ nv₁ logw₁ logc₁ : ℕ}
variable {Enc₁ Salt₁ : Type} [DecidableEq Enc₁] [Inhabited Salt₁]
variable {Ctx₁ Msg₁ Out₁ : Type} [DecidableEq Ctx₁] [DecidableEq Msg₁] [Inhabited Msg₁]
variable {Aux₁ Aux₁' : Type} {respondFuel₁ revealFuel₁ : ℕ}
variable {Cand₂ F₂ Equations₂ Witness₂ : Type} [Fintype Cand₂] [Nonempty Cand₂] [Field F₂]
  [Fintype F₂] [DecidableEq F₂] [SumcheckV1Interp F₂] [Fintype Equations₂] [DecidableEq Equations₂]
variable {nc₂ nv₂ logw₂ logc₂ : ℕ}
variable {Enc₂ Salt₂ : Type} [DecidableEq Enc₂] [Inhabited Salt₂]
variable {Ctx₂ Msg₂ Out₂ : Type} [DecidableEq Ctx₂] [DecidableEq Msg₂] [Inhabited Msg₂]
variable {Aux₂ Aux₂' : Type} {respondFuel₂ revealFuel₂ : ℕ}
omit [Fintype Fmac] in
/-- **A side's merged acceptance is its compiled verifier on its own coordinates.** The event
reads `(toFSFamily.sideBound.toMacBound …).accepts`; at
`ω` it is `Accepts (v1K …) V …` at the absorbed coordinate `restOf ι ω.2` and the side's tape
`ω.2 ∘ ι`. -/
theorem toMacBound_accepts_iff {R : Row} {hR : R.Valid} {hr : 0 < R.params.row.openings}
    {Tm : ℕ} {ι : Fin (R.fsLen N₁) → Fin Tm}
    {codec₁ : Codec Salt₁ (Col F₁ R.params.nw R.params.nq) D Enc₁} {dec₁ : RoleDecoders codec₁}
    {dom₁ : LigeroFamily.ReedSolomon.Domain F₁ R.params.row.openings R.params.q R.params.row.n}
    {V₁ : Code C F₁ (LigeroV1LayerStep.Chal F₁ Equations₁ R.params.nw R.params.nq)
      (LigeroV1LayerStep.Qry R.params.row) Msg₁ logw₁ logc₁} {msgOf₁ : Out₁ → ℕ → Msg₁}
    (L : CompiledFSFamily R hR hr (Rest ι → C) C Cand₁ F₁ Equations₁ Witness₁ nc₁ nv₁ logw₁ logc₁
      Ctx₁ Msg₁ Out₁ N₁ Aux₁ Aux₁' tlen respondFuel₁ revealFuel₁ dec₁ dom₁ V₁ msgOf₁)
    {keyA : (Fin tlen → D) × (Fin Tm → C) → Fmac}
    {keyB tag : (Fin tlen → D) × (Fin Tm → C) → Fin nblk → Fmac}
    (common : Witness₁ → Fin nblk → Fmac)
    (hrow : ∀ (ω : (Fin tlen → D) × (Fin Tm → C)) (a : Witness₁),
      L.toFSFamily.sideBound.mergedAccepts ω → L.toFSFamily.sideBound.mergedGood ω a →
      macTag (keyA ω) (keyB ω) (common a) = tag ω)
    (ω : (Fin tlen → D) × (Fin Tm → C)) :
    (L.toFSFamily.sideBound.toMacBound common hrow).accepts ω ↔
      L.accepts (restOf ι ω.2) (ω.1, ω.2 ∘ ι) :=
  L.toFSFamily_accepts_iff (restOf ι ω.2) (ω.1, ω.2 ∘ ι)

end Headline

end LfzkV1.CompiledLongfellowTwoField
