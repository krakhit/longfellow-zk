import LfzkV1.NizkAdaptiveS
import LfzkV1.CompiledLongfellowAdaptive

/-!
# The compiled Longfellow verifier against a re-committing prover, at the mixed accounting

`LfzkV1.CompiledLongfellowAdaptive`'s headlines with the list factor dropped at the two Ligero slots
(`LfzkV1.NizkAdaptiveS`).  The verifier (`AcceptsAt`: `FieldPass` and the Merkle-compiled V1 policy
on the root's statement), the prover, `hlig` and `hright` (theorems, as there) and every remaining
premise are unchanged; the bound uses the mixed accounting.

## What is still a hypothesis

Exactly `CompiledLongfellowAdaptive.row_adaptive_ratio_le_v1`'s and
`twofield_adaptive_compiled_ratio_le`'s premises: the protocol instance, `Matches`, `hfalse` (at a
failing context the root's Ligero statement is false), `hfail`, and — two-field — the MAC rows.
This is still the clear-verifier model (`FieldPass` checks the sumcheck rounds in the clear and the
Ligero statement is fixed by the root); `LfzkV1.CompiledZk` is the deployed zero-knowledge verifier.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LfzkV1.CompiledLongfellowAdaptive

open Finset Bcs Bcs.AdaptiveCommit Merkle Merkle.MH Merkle.RandomOracle
  Merkle.RandomOracle.TwoOracleTree RbrLongfellow LfzkV1.NizkGrinding LfzkV1.NizkAdaptive
  LfzkV1.CompiledLongfellow
open scoped Classical

section RowS

open LfzkV1.CertifiedV1

variable {C Cand : Type} [Fintype C] [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand]
variable {F Equations Witness : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckV1Interp F]
  [Fintype Equations] [DecidableEq Equations]
variable {logw logc nc nv : ℕ}
variable {Enc D Salt : Type} [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc]
  [Inhabited Salt]
variable {Msg Out : Type} [DecidableEq Msg] [Inhabited Msg] {tA N : ℕ}

/--
**A certified V1 row at the compiled Longfellow verifier, against a re-committing prover, at the
mixed accounting.**

```text
Pr[ AcceptsAt (v1K …) …  ∧  Fails(context) ]
    ≤  R.boundS  +  N · R.fsCoefficientS  +  R.tape · (L + N) / 2^digestBits
```

`row_adaptive_ratio_le_v1` with `CertifiedV1.Row.adaptive_ratio_leS` in place of
`Row.adaptive_ratio_le`; the premises are the same.
-/
theorem row_adaptive_ratio_le_v1S {R : Row} (h : R.Valid) (hr : 0 < R.params.row.openings)
    {codec : Codec Salt (Col F R.params.nw R.params.nq) D Enc} (dec : RoleDecoders codec)
    (V : Code C F (LigeroV1LayerStep.Chal F Equations R.params.nw R.params.nq)
      (LigeroV1LayerStep.Qry R.params.row) Msg logw logc)
    (dom : LigeroFamily.ReedSolomon.Domain F R.params.row.openings R.params.q R.params.row.n)
    (stmt : D → LigeroFamily.ConstraintSystem F R.params.nw R.params.nq R.params.q Equations)
    (respOf : Msg → LigeroFamily.Response F R.params.row.openings R.params.q R.params.row.n 1)
    (body : TwoOracleTree Enc D (Point D Msg C R.params.nl R.params.rounds) C Out tA N)
    (dflt : C) (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim R.params.row.n Salt (Col F R.params.nw R.params.nq) D)
    {Fails : D × List (Enc × D) → Prop}
    (hF : Fintype.card F = R.params.row.fieldSize)
    (hfalse : ∀ κ, Fails κ → ¬ (stmt κ.1).Language)
    (H : ∀ _κ : D × List (Enc × D), RbrLongfellow.Honest F Cand logw logc)
    (Sat : D × List (Enc × D) → Cand → Prop)
    (Ffam : ∀ κ, RbrSplit.FieldData C F (LigeroV1LayerStep.Chal F Equations R.params.nw R.params.nq)
        (LigeroV1LayerStep.Qry R.params.row) Cand Witness nc nv logw logc (H κ) (Sat κ))
    (hexact : ∀ κ, (Ffam κ).Exact)
    (MD : ∀ κ, MsgData C Msg (H κ))
    (hmatch : ∀ κ, Matches V (Ffam κ) (MD κ))
    (hfail : ∀ κ, Fails κ → ∀ cand : Cand, ¬ Sat κ cand)
    (htA : tA ≤ R.commitFuel) (htape : 2 * R.params.row.n + tA ≤ R.tape)
    (hcand : Fintype.card Cand = R.cardCand)
    (hD : Fintype.card D = 2 ^ R.params.digestBits) :
    ((univ.filter fun ω : (Fin R.tape → D) × (Fin (R.fsLen N) → C) =>
        AcceptsAt (v1K (Row.rowValid h) dom (Row.hkrow h) hr) V codec
            (lfSetup body dflt rootOf msgOf) (lfCheck codec claimOf) rootOf msgOf claimOf
            (rootStatement rootOf stmt) respOf id ω.1 ω.2 ∧
          Fails ((lfSetup body dflt rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ R.tape * (Fintype.card C : ℚ) ^ R.fsLen N)
      ≤ R.boundS + N * R.fsCoefficientS
        + ((R.tape * (Rounds.Role.length R.params.nl R.params.rounds + N) : ℕ) : ℚ)
          / 2 ^ R.params.digestBits := by
  refine le_trans (le_of_eq ?_)
    (Row.adaptive_ratio_leS h dec (guarded (v1K (Row.rowValid h) dom (Row.hkrow h) hr)) body dflt
      rootOf msgOf claimOf (statementOfAt V msgOf (rootStatement rootOf stmt) id)
      (responseOfAt R.params.nl R.params.rounds respOf msgOf) (challengeOfAt V id) (queryOfAt V id)
      hF (accR (Row.rowValid h) dom (Row.hkrow h) hr dec stmt respOf)
      (fun κ hκ => exists_msgLigeroData C Msg (Row.rowValid h) (Row.coreRows h) hF dom (Row.hkrow h)
        (extractedInstance (Row.rowValid h) dom (Row.hkrow h) hr dec (stmt κ.1) κ.1 κ.2)
        (hfalse κ hκ) respOf)
      H Sat Ffam hexact MD hfail
      (fun mt ct _ hacc hexp => hright_v1 (Row.rowValid h) dom (Row.hkrow h) hr dec V body dflt
        rootOf msgOf claimOf stmt respOf (Ffam _) (MD _) (hmatch _) mt ct hacc hexp)
      htA htape hcand hD)
  congr 3
  refine Finset.filter_congr fun ω _ => ?_
  rw [acceptsAt_iff_joint]

end RowS

/-! ## Two fields -/

section TwoFieldS

open LfzkV1.CertifiedV1 LfzkV1.NizkAdaptiveTwoField LfzkV1.TwoFieldV1Rows LfzkV1.Mac

variable {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {D : Type} [Fintype D] [DecidableEq D] [Inhabited D]
variable {Enc X Out : Type} [DecidableEq Enc]
variable {Fmac : Type} [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {nblk : ℕ}
variable {Cand₁ F₁ Equations₁ Witness₁ Msg₁ : Type} [Fintype Cand₁] [Nonempty Cand₁] [Field F₁]
  [Fintype F₁] [DecidableEq F₁] [SumcheckV1Interp F₁] [Fintype Equations₁] [DecidableEq Equations₁]
  [DecidableEq Msg₁] [Inhabited Msg₁] {nc₁ nv₁ logw₁ logc₁ : ℕ}
variable {Cand₂ F₂ Equations₂ Witness₂ Msg₂ : Type} [Fintype Cand₂] [Nonempty Cand₂] [Field F₂]
  [Fintype F₂] [DecidableEq F₂] [SumcheckV1Interp F₂] [Fintype Equations₂] [DecidableEq Equations₂]
  [DecidableEq Msg₂] [Inhabited Msg₂] {nc₂ nv₂ logw₂ logc₂ : ℕ}
variable {Salt₁ Salt₂ : Type} [Inhabited Salt₁] [Inhabited Salt₂]

/--
**Two-field Longfellow at the compiled verifiers, against one re-committing prover with a hashed
MAC key, at the mixed accounting.**  `twofield_adaptive_compiled_ratio_le` with
`NizkAdaptiveTwoField.twofield_adaptive_ratio_leS`; the premises are the same.
-/
theorem twofield_adaptive_compiled_ratio_leS {R₁ R₂ : Row} (h₁ : R₁.Valid) (h₂ : R₂.Valid)
    (hr₁ : 0 < R₁.params.row.openings) (hr₂ : 0 < R₂.params.row.openings) {tA N : ℕ}
    {codec₁ : Codec Salt₁ (Col F₁ R₁.params.nw R₁.params.nq) D Enc} {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ R₂.params.nw R₂.params.nq) D Enc} {dec₂ : RoleDecoders codec₂}
    (L₁ : CompiledSide R₁ h₁ hr₁ C Cand₁ F₁ Equations₁ Witness₁ Msg₁ nc₁ nv₁ logw₁ logc₁ X dec₁
      Prod.fst)
    (L₂ : CompiledSide R₂ h₂ hr₂ C Cand₂ F₂ Equations₂ Witness₂ Msg₂ nc₂ nv₂ logw₂ logc₂ X dec₂
      Prod.snd)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds
      R₂.params.rounds) C Out tA N)
    (dflt : C) (rootOf₁ rootOf₂ : Out → D) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim R₁.params.row.n Salt₁ (Col F₁ R₁.params.nw R₁.params.nq) D)
    (claimOf₂ : Out → OpeningClaim R₂.params.row.n Salt₂ (Col F₂ R₂.params.nw R₂.params.nq) D)
    (hcand₁ : Fintype.card Cand₁ = R₁.cardCand) (hcand₂ : Fintype.card Cand₂ = R₂.cardCand)
    (hD₁ : Fintype.card D = 2 ^ R₁.params.digestBits)
    (hD₂ : Fintype.card D = 2 ^ R₂.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : Witness₁ → Fin nblk → Fmac) (common₂ : Witness₂ → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin R₁.tape → D) (ct : Fin (len2 R₁ R₂ + N) → C) (a : Witness₁),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      L₁.accepts S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ pubOf
        (len2_pos R₁ R₂) (slice1 R₁ R₂) mt ct →
      L₁.Good (sideCtx S pubOf (len2_pos R₁ R₂) mt ct) a →
      macTag (aP (S.context mt ct) + decode (S.challenges mt ct ⟨0, len2_pos R₁ R₂⟩))
        (keyB (S.proof mt ct)) (common₁ a) = tagOf (S.proof mt ct))
    (hrow₂ : ∀ (mt : Fin R₁.tape → D) (ct : Fin (len2 R₁ R₂ + N) → C) (a : Witness₂),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      L₂.accepts S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ pubOf
        (len2_pos R₁ R₂) (slice2 R₁ R₂) mt ct →
      L₂.Good (sideCtx S pubOf (len2_pos R₁ R₂) mt ct) a →
      macTag (aP (S.context mt ct) + decode (S.challenges mt ct ⟨0, len2_pos R₁ R₂⟩))
        (keyB (S.proof mt ct)) (common₂ a) = tagOf (S.proof mt ct))
    (htA₁ : tA ≤ R₁.commitFuel) (htA₂ : tA ≤ R₂.commitFuel)
    (htape : 2 * R₂.params.row.n + 2 * R₁.params.row.n + tA ≤ R₁.tape)
    (htape₂ : R₁.tape = R₂.tape) :
    ((univ.filter fun ω : (Fin R₁.tape → D) × (Fin (len2 R₁ R₂ + N) → C) =>
        L₁.accepts (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ pubOf
            (len2_pos R₁ R₂) (slice1 R₁ R₂) ω.1 ω.2 ∧
          L₂.accepts (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ pubOf
            (len2_pos R₁ R₂) (slice2 R₁ R₂) ω.1 ω.2 ∧
          ¬ ∃ a₁ a₂,
            L₁.Good (sideCtx (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂) pubOf
              (len2_pos R₁ R₂) ω.1 ω.2) a₁ ∧
            L₂.Good (sideCtx (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂) pubOf
              (len2_pos R₁ R₂) ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ R₁.tape * (Fintype.card C : ℚ) ^ (len2 R₁ R₂ + N))
      ≤ R₁.boundS + R₂.boundS + 1 / (Fintype.card Fmac : ℚ)
        + N * max (max R₁.fsCoefficientS R₂.fsCoefficientS) (1 / (Fintype.card Fmac : ℚ))
        + 2 * (((R₁.tape * (len2 R₁ R₂ + N) : ℕ) : ℚ) / 2 ^ R₁.params.digestBits) := by
  have hroot₁ : ∀ out, Prod.fst ((setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂).keyOut out)
      = rootOf₁ out := fun _ => rfl
  have hroot₂ : ∀ out, Prod.snd ((setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂).keyOut out)
      = rootOf₂ out := fun _ => rfl
  refine le_trans (le_of_eq ?_)
    (twofield_adaptive_ratio_leS h₁ dec₁ dec₂
      (guarded (v1K (Row.rowValid h₁) L₁.dom (Row.hkrow h₁) hr₁))
      (guarded (v1K (Row.rowValid h₂) L₂.dom (Row.hkrow h₂) hr₂))
      body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂
      (statementOfAt L₁.V msgOf₁ (L₁.stmtOf rootOf₁ pubOf (len2_pos R₁ R₂)) (slice1 R₁ R₂))
      (responseOfAt R₁.params.nl R₁.params.rounds L₁.respOf msgOf₁)
      (challengeOfAt L₁.V (slice1 R₁ R₂)) (queryOfAt L₁.V (slice1 R₁ R₂))
      (statementOfAt L₂.V msgOf₂ (L₂.stmtOf rootOf₂ pubOf (len2_pos R₁ R₂)) (slice2 R₁ R₂))
      (responseOfAt R₂.params.nl R₂.params.rounds L₂.respOf msgOf₂)
      (challengeOfAt L₂.V (slice2 R₁ R₂)) (queryOfAt L₂.V (slice2 R₁ R₂))
      L₁.toSide L₂.toSide L₁.hF L₂.hF hcand₁ hcand₂ hD₁ hD₂ aP decode kmac hbal hmac keyB tagOf
      common₁ common₂
      (fun mt ct _ hacc hexp => L₁.hright _ _ rootOf₁ hroot₁ msgOf₁ claimOf₁ pubOf (len2_pos R₁ R₂)
        (slice1 R₁ R₂) mt ct hacc hexp)
      (fun mt ct _ hacc hexp => L₂.hright _ _ rootOf₂ hroot₂ msgOf₂ claimOf₂ pubOf (len2_pos R₁ R₂)
        (slice2 R₁ R₂) mt ct hacc hexp)
      (fun mt ct a hacc hgood => hrow₁ mt ct a
        ((L₁.accepts_iff_joint _ _ rootOf₁ msgOf₁ claimOf₁ pubOf (len2_pos R₁ R₂) (slice1 R₁ R₂)
          mt ct).mpr hacc) hgood)
      (fun mt ct a hacc hgood => hrow₂ mt ct a
        ((L₂.accepts_iff_joint _ _ rootOf₂ msgOf₂ claimOf₂ pubOf (len2_pos R₁ R₂) (slice2 R₁ R₂)
          mt ct).mpr hacc) hgood)
      htA₁ htA₂ htape htape₂)
  congr 3
  refine Finset.filter_congr fun ω _ => ?_
  rw [L₁.accepts_iff_joint, L₂.accepts_iff_joint]
  exact Iff.rfl

end TwoFieldS

end LfzkV1.CompiledLongfellowAdaptive
