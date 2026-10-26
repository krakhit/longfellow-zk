import LfzkV1.TwoFieldV1
import LfzkV1.TwoFieldV1Fields
import LfzkV1.ProfileMonoV1

/-!
# Validated two-field Ligero V1 rows

`TwoFieldRowV1` pairs two certified rows and checks their field sizes, shared hash tape,
Merkle fuel, Reed–Solomon domains, composed error and proof size. The generic
`nizk_ratio_le` theorem composes the two sides through the MAC.

This file also constructs exactly balanced coin decoders and proves that the
fuel and domain premises hold for any valid row. Concrete v7 instances and
their joint satisfiability checks are in `TwoFieldV7Rows`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LfzkV1.TwoFieldV1Rows

open Finset

/-! ## Exactly balanced decoders on one shared alphabet -/

/-- A decoder `C → Y` that is at most `k`-to-one, with `k · |Y| ≤ |C|`: exactly balanced. -/
structure ExactDecoder (C Y : Type) [Fintype C] [Fintype Y] [DecidableEq Y] where
  decode : C → Y
  k : ℕ
  hbal : ∀ y : Y, (univ.filter fun c : C => decode c = y).card ≤ k
  hexact : k * Fintype.card Y ≤ Fintype.card C

theorem card_filter_comp_fst {A B Y : Type} [Fintype A] [Fintype B] [DecidableEq Y]
    (d : A → Y) (y : Y) :
    (univ.filter fun c : A × B => d c.1 = y).card
      = (univ.filter fun a : A => d a = y).card * Fintype.card B := by
  rw [← Finset.card_univ (α := B), ← Finset.card_product]
  congr 1
  ext ⟨a, b⟩
  simp

theorem card_filter_comp_snd {A B Y : Type} [Fintype A] [Fintype B] [DecidableEq Y]
    (d : B → Y) (y : Y) :
    (univ.filter fun c : A × B => d c.2 = y).card
      = Fintype.card A * (univ.filter fun b : B => d b = y).card := by
  rw [← Finset.card_univ (α := A), ← Finset.card_product]
  congr 1
  ext ⟨a, b⟩
  simp

namespace ExactDecoder

/-- The identity is exactly balanced. -/
def self (Y : Type) [Fintype Y] [DecidableEq Y] : ExactDecoder Y Y where
  decode y := y
  k := 1
  hbal y := by simp [Finset.filter_eq']
  hexact := by simp

/-- Read the first coordinate: the balance multiplies by the second coordinate's size. -/
def fst {A Y : Type} [Fintype A] [Fintype Y] [DecidableEq Y] (d : ExactDecoder A Y)
    (B : Type) [Fintype B] : ExactDecoder (A × B) Y where
  decode c := d.decode c.1
  k := d.k * Fintype.card B
  hbal y := by
    rw [card_filter_comp_fst]
    exact Nat.mul_le_mul_right _ (d.hbal y)
  hexact := by
    rw [Fintype.card_prod]
    calc d.k * Fintype.card B * Fintype.card Y = d.k * Fintype.card Y * Fintype.card B := by ring
      _ ≤ Fintype.card A * Fintype.card B := Nat.mul_le_mul_right _ d.hexact

/-- Read the second coordinate. -/
def snd {B Y : Type} [Fintype B] [Fintype Y] [DecidableEq Y] (d : ExactDecoder B Y)
    (A : Type) [Fintype A] : ExactDecoder (A × B) Y where
  decode c := d.decode c.2
  k := Fintype.card A * d.k
  hbal y := by
    rw [card_filter_comp_snd]
    exact Nat.mul_le_mul_left _ (d.hbal y)
  hexact := by
    rw [Fintype.card_prod]
    calc Fintype.card A * d.k * Fintype.card Y = Fintype.card A * (d.k * Fintype.card Y) := by
          ring
      _ ≤ Fintype.card A * Fintype.card B := Nat.mul_le_mul_left _ d.hexact

end ExactDecoder

section Coins

variable (F X Q : Type) [Field F] [Fintype F] [DecidableEq F] [Fintype X] [DecidableEq X]
  [Fintype Q] [DecidableEq Q]

/-- One side's own coins: a Ligero challenge, a query, and a layer pair. -/
abbrev SideCoins := X × Q × (F × F)

/-- The side's Ligero challenge decoder. -/
def chalD : ExactDecoder (SideCoins F X Q) X := (ExactDecoder.self X).fst (Q × (F × F))

/-- The side's query decoder. -/
def queryD : ExactDecoder (SideCoins F X Q) Q :=
  ((ExactDecoder.self Q).fst (F × F)).snd X

/-- The side's pair decoder. -/
def pairD : ExactDecoder (SideCoins F X Q) (F × F) :=
  ((ExactDecoder.self (F × F)).snd Q).snd X

/-- The side's field-element decoder: the first coordinate of the pair. -/
def eltD : ExactDecoder (SideCoins F X Q) F :=
  (((ExactDecoder.self F).fst F).snd Q).snd X

end Coins

section TwoCoins

variable (F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac : Type)
  [Field F₁] [Fintype F₁] [DecidableEq F₁] [Fintype X₁] [DecidableEq X₁]
  [Fintype Q₁] [DecidableEq Q₁]
  [Field F₂] [Fintype F₂] [DecidableEq F₂] [Fintype X₂] [DecidableEq X₂]
  [Fintype Q₂] [DecidableEq Q₂]
  [Fintype Fmac] [DecidableEq Fmac]

/-- **One coin alphabet for the whole two-field argument**: side 1's coins, side 2's coins, and the
MAC key coin. -/
abbrev TwoFieldCoins := SideCoins F₁ X₁ Q₁ × (SideCoins F₂ X₂ Q₂ × Fmac)

/-- Side 1's four decoders on the shared alphabet. -/
def side₁ : ExactDecoder (TwoFieldCoins F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac) (F₁ × F₁) ×
    ExactDecoder (TwoFieldCoins F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac) F₁ ×
    ExactDecoder (TwoFieldCoins F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac) X₁ ×
    ExactDecoder (TwoFieldCoins F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac) Q₁ :=
  ((pairD F₁ X₁ Q₁).fst _, (eltD F₁ X₁ Q₁).fst _, (chalD F₁ X₁ Q₁).fst _,
    (queryD F₁ X₁ Q₁).fst _)

/-- Side 2's four decoders on the shared alphabet. -/
def side₂ : ExactDecoder (TwoFieldCoins F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac) (F₂ × F₂) ×
    ExactDecoder (TwoFieldCoins F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac) F₂ ×
    ExactDecoder (TwoFieldCoins F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac) X₂ ×
    ExactDecoder (TwoFieldCoins F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac) Q₂ :=
  (((pairD F₂ X₂ Q₂).fst Fmac).snd _, ((eltD F₂ X₂ Q₂).fst Fmac).snd _,
    ((chalD F₂ X₂ Q₂).fst Fmac).snd _, ((queryD F₂ X₂ Q₂).fst Fmac).snd _)

/-- The MAC key's decoder on the shared alphabet. -/
def macD : ExactDecoder (TwoFieldCoins F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac) Fmac :=
  ((ExactDecoder.self Fmac).snd (SideCoins F₂ X₂ Q₂)).snd (SideCoins F₁ X₁ Q₁)

end TwoCoins

/-! ### Re-decoding a field half -/

section Redecode

variable {C F X Q Cand Witness : Type} [Fintype C] [Field F] [Fintype F] [DecidableEq F]
  [SumcheckV1Interp F] [Fintype X] [DecidableEq X] [Fintype Q] [DecidableEq Q]
variable {nc nv logw logc : ℕ} {H : RbrLongfellow.Honest F Cand logw logc} {Sat : Cand → Prop}

/-- **Re-decode a field half.**  Replace its four coin decoders and their balances; nothing else in
`RbrSplit.FieldData` reads them. -/
def withDecoders (FD : RbrSplit.FieldData C F X Q Cand Witness nc nv logw logc H Sat)
    (dp : ExactDecoder C (F × F)) (dF : ExactDecoder C F) (dX : ExactDecoder C X)
    (dQ : ExactDecoder C Q) : RbrSplit.FieldData C F X Q Cand Witness nc nv logw logc H Sat :=
  { FD with
    decodePair := dp.decode, decodeF := dF.decode, decodeChal := dX.decode,
    decodeQuery := dQ.decode, kpair := dp.k, k := dF.k, kchal := dX.k, kq := dQ.k,
    hbalPair := dp.hbal, hbalF := dF.hbal, hbalChal := dX.hbal, hbalQuery := dQ.hbal }

/-- **Exactly balanced decoders make a field half `Exact`.** -/
theorem withDecoders_exact (FD : RbrSplit.FieldData C F X Q Cand Witness nc nv logw logc H Sat)
    (dp : ExactDecoder C (F × F)) (dF : ExactDecoder C F) (dX : ExactDecoder C X)
    (dQ : ExactDecoder C Q) : (withDecoders FD dp dF dX dQ).Exact := by
  refine ⟨?_, dF.hexact, dX.hexact, dQ.hexact⟩
  have := dp.hexact
  rwa [Fintype.card_prod] at this

omit [SumcheckV1Interp F] in
/-- **The V1 pair budget always has room for the layer-0 decoder.**  Over a non-empty alphabet an
exactly balanced pair decoder forces `|F|² ≤ |C|`, so `⌊2|C|/|F|⌋ ≥ 2|F|`: the bound the V3 rows'
`bpair` numerals violated (`RbrLongfellow.LayerStepData.two_card_le_bpair`) holds automatically. -/
theorem pair_room [Nonempty C] (dp : ExactDecoder C (F × F)) :
    2 * Fintype.card F ≤ CertifiedV1.pairBudget (Fintype.card C) (Fintype.card F) := by
  obtain ⟨c⟩ := ‹Nonempty C›
  have hk : 1 ≤ dp.k := le_trans
    (Finset.card_pos.mpr ⟨c, by simp⟩) (dp.hbal (dp.decode c))
  have hF : 0 < Fintype.card F := Fintype.card_pos
  have hsq : Fintype.card F * Fintype.card F ≤ Fintype.card C := by
    have := dp.hexact
    rw [Fintype.card_prod] at this
    calc Fintype.card F * Fintype.card F = 1 * (Fintype.card F * Fintype.card F) := by ring
      _ ≤ dp.k * (Fintype.card F * Fintype.card F) := Nat.mul_le_mul_right _ hk
      _ ≤ Fintype.card C := this
  unfold CertifiedV1.pairBudget
  rw [Nat.le_div_iff_mul_le hF]
  calc 2 * Fintype.card F * Fintype.card F = 2 * (Fintype.card F * Fintype.card F) := by ring
    _ ≤ 2 * Fintype.card C := Nat.mul_le_mul_left 2 hsq

/-- **LayerStep's field budgets hold at the V1 numerals**: `RbrSplit.Budgets`' four field-round
inequalities at `bpair = bround = ⌊2|C|/|F|⌋`, `bin = ⌊|C|/|F|⌋`, for any re-decoded field half. -/
theorem field_budgets_of_exact (FD : RbrSplit.FieldData C F X Q Cand Witness nc nv logw logc H Sat)
    (dp : ExactDecoder C (F × F)) (dF : ExactDecoder C F) (dX : ExactDecoder C X)
    (dQ : ExactDecoder C Q) :
    (withDecoders FD dp dF dX dQ).kpair * (2 * Fintype.card F)
        ≤ CertifiedV1.pairBudget (Fintype.card C) (Fintype.card F) ∧
      (withDecoders FD dp dF dX dQ).k * 1
        ≤ CertifiedV1.pairBudget (Fintype.card C) (Fintype.card F) ∧
      (withDecoders FD dp dF dX dQ).k * 2
        ≤ CertifiedV1.pairBudget (Fintype.card C) (Fintype.card F) ∧
      (withDecoders FD dp dF dX dQ).k * 1
        ≤ CertifiedV1.inBudget (Fintype.card C) (Fintype.card F) :=
  (withDecoders_exact FD dp dF dX dQ).field_budgets

end Redecode

/--
**The decoders can be exactly balanced, for both sides and the MAC at once.**

On `TwoFieldCoins`, any field half of side 1 and any field half of side 2 re-decode to `Exact` field
halves (`hexact` of both `V1Family`s), and the MAC key decoder satisfies `kmac · |Fmac| ≤ |C|`
(`hmac` of `TwoFieldV1.twofield_v1_ratio_le_exact`).  The two-field analogue of
`RbrSplit.product_coins_exact`.
-/
theorem twoField_coins_exact {F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac : Type}
    [Field F₁] [Fintype F₁] [DecidableEq F₁] [SumcheckV1Interp F₁] [Fintype X₁] [DecidableEq X₁]
    [Fintype Q₁] [DecidableEq Q₁]
    [Field F₂] [Fintype F₂] [DecidableEq F₂] [SumcheckV1Interp F₂] [Fintype X₂] [DecidableEq X₂]
    [Fintype Q₂] [DecidableEq Q₂]
    [Fintype Fmac] [DecidableEq Fmac]
    {Cand₁ Witness₁ Cand₂ Witness₂ : Type} {nc₁ nv₁ logw₁ logc₁ nc₂ nv₂ logw₂ logc₂ : ℕ}
    {H₁ : RbrLongfellow.Honest F₁ Cand₁ logw₁ logc₁} {Sat₁ : Cand₁ → Prop}
    {H₂ : RbrLongfellow.Honest F₂ Cand₂ logw₂ logc₂} {Sat₂ : Cand₂ → Prop}
    (FD₁ : RbrSplit.FieldData (TwoFieldCoins F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac) F₁ X₁ Q₁ Cand₁ Witness₁
      nc₁ nv₁ logw₁ logc₁ H₁ Sat₁)
    (FD₂ : RbrSplit.FieldData (TwoFieldCoins F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac) F₂ X₂ Q₂ Cand₂ Witness₂
      nc₂ nv₂ logw₂ logc₂ H₂ Sat₂) :
    (withDecoders FD₁ (side₁ F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac).1 (side₁ F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac).2.1
        (side₁ F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac).2.2.1 (side₁ F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac).2.2.2).Exact ∧
      (withDecoders FD₂ (side₂ F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac).1 (side₂ F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac).2.1
        (side₂ F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac).2.2.1 (side₂ F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac).2.2.2).Exact ∧
      (∀ x : Fmac, (univ.filter fun c : TwoFieldCoins F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac =>
          (macD F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac).decode c = x).card
        ≤ (macD F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac).k) ∧
      (macD F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac).k * Fintype.card Fmac
        ≤ Fintype.card (TwoFieldCoins F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac) :=
  ⟨withDecoders_exact _ _ _ _ _, withDecoders_exact _ _ _ _ _,
    (macD F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac).hbal, (macD F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac).hexact⟩

/-! ## The two-field row -/

/-- One certified **two-field** V1 row: the two sides of Protocol 3.8 and the MAC field's size. -/
structure TwoFieldRowV1 where
  /-- The prime-field side — ECDSA over `P-256`'s base field. -/
  ecdsa : CertifiedV1.Row
  /-- The binary side — SHA-256 over `GF(2^128)`. -/
  sha : CertifiedV1.Row
  /-- `|Fmac|`; the MAC slot costs `1/|Fmac|` at an exactly balanced key decoder. -/
  macFieldSize : ℕ
  /-- The composed security target, in bits. -/
  lam : ℕ
  /-- Modelled composed proof size, in bytes. -/
  sizeBound : ℕ

namespace TwoFieldRowV1

variable (R : TwoFieldRowV1)

/-- The composed bound — `TwoFieldV1.twofield_v1_ratio_le_exact`'s right-hand side. -/
def bound : ℚ := R.ecdsa.bound + R.sha.bound + 1 / (R.macFieldSize : ℚ)

/-- A checked two-field row; see the module docstring for the conjuncts. -/
def Valid : Prop :=
  R.ecdsa.Valid ∧ R.sha.Valid ∧
    R.ecdsa.tape = R.sha.tape ∧
    R.ecdsa.params.digestBits = R.sha.params.digestBits ∧
    R.ecdsa.params.row.fieldOrder ≠ 0 ∧ R.sha.params.row.fieldOrder = 0 ∧
    (2 * R.ecdsa.params.row.n + R.ecdsa.commitFuel)
        + (2 * R.sha.params.row.n + R.sha.commitFuel) < R.sha.tape ∧
    R.ecdsa.params.row.openings + R.ecdsa.params.q + R.ecdsa.params.row.n
        ≤ R.ecdsa.params.row.fieldSize ∧
    R.sha.params.row.openings + R.sha.params.q + R.sha.params.row.n
        ≤ R.sha.params.row.fieldSize ∧
    0 < R.macFieldSize ∧
    R.bound ≤ (1 : ℚ) / 2 ^ R.lam ∧
    R.ecdsa.params.proofBytes + R.sha.params.proofBytes ≤ R.sizeBound

instance : Decidable R.Valid := by
  unfold Valid CertifiedV1.Row.Valid LigeroFamily.CoreRowsNonempty
  infer_instance

def validBool : Bool := decide R.Valid

/-- The recorded `lam` is the composed bound's exact integer bit level. -/
def Sharp : Prop := ¬ R.bound ≤ (1 : ℚ) / 2 ^ (R.lam + 1)

instance : Decidable R.Sharp := by unfold Sharp; infer_instance

def sharpBool : Bool := decide R.Sharp

variable {R}

theorem ecdsa_valid (h : R.Valid) : R.ecdsa.Valid := h.1
theorem sha_valid (h : R.Valid) : R.sha.Valid := h.2.1

/-- **One hash tape.** -/
theorem tape_eq (h : R.Valid) : R.ecdsa.tape = R.sha.tape := h.2.2.1

/-- **One digest.** -/
theorem digest_eq (h : R.Valid) : R.ecdsa.params.digestBits = R.sha.params.digestBits :=
  h.2.2.2.1

/-- **Two fields**, a prime one and a binary one. -/
theorem two_fields (h : R.Valid) :
    R.ecdsa.params.row.fieldOrder ≠ 0 ∧ R.sha.params.row.fieldOrder = 0 :=
  ⟨h.2.2.2.2.1, h.2.2.2.2.2.1⟩

/-- **Room for both sides' leaves and commitment fuels on the shared tape.** -/
theorem room (h : R.Valid) :
    (2 * R.ecdsa.params.row.n + R.ecdsa.commitFuel)
      + (2 * R.sha.params.row.n + R.sha.commitFuel) < R.sha.tape := h.2.2.2.2.2.2.1

theorem rs_fits_ecdsa (h : R.Valid) :
    R.ecdsa.params.row.openings + R.ecdsa.params.q + R.ecdsa.params.row.n
      ≤ R.ecdsa.params.row.fieldSize := h.2.2.2.2.2.2.2.1

theorem rs_fits_sha (h : R.Valid) :
    R.sha.params.row.openings + R.sha.params.q + R.sha.params.row.n
      ≤ R.sha.params.row.fieldSize := h.2.2.2.2.2.2.2.2.1

theorem mac_pos (h : R.Valid) : 0 < R.macFieldSize := h.2.2.2.2.2.2.2.2.2.1

theorem target (h : R.Valid) : R.bound ≤ (1 : ℚ) / 2 ^ R.lam := h.2.2.2.2.2.2.2.2.2.2.1

theorem size (h : R.Valid) :
    R.ecdsa.params.proofBytes + R.sha.params.proofBytes ≤ R.sizeBound :=
  h.2.2.2.2.2.2.2.2.2.2.2

theorem valid_of_validBool (h : R.validBool = true) : R.Valid := of_decide_eq_true h

/-! ### Non-vacuity, at every valid row -/

/--
**The fuel premises are jointly satisfiable.**  On the shared tape `tlen = sha.tape`, at Ligero's
`n` leaves per side, both sides' `ht₁`, `hT`, `hT1` hold at once, with the tape's spare room handed
to the SHA side's adversary as opening fuel — and both sides' leaves and fuels fit together.  Neither
side records `commitFuel = tape`, the V3 rows' failure (`TwoFieldLongfellow.twoFieldRow_fuel_unsat`).
-/
theorem fuel_satisfiable (h : R.Valid) :
    R.ecdsa.tape = R.sha.tape ∧
      R.ecdsa.commitFuel ≤ R.sha.tape ∧ R.sha.commitFuel ≤ R.sha.tape ∧ 1 ≤ R.sha.tape ∧
      2 * R.ecdsa.params.row.n + (0 + 0) + R.ecdsa.commitFuel ≤ R.sha.tape ∧
      2 * R.sha.params.row.n
          + (0 + (R.sha.tape - ((2 * R.ecdsa.params.row.n + R.ecdsa.commitFuel)
            + (2 * R.sha.params.row.n + R.sha.commitFuel))))
          + R.sha.commitFuel ≤ R.sha.tape ∧
      (2 * R.ecdsa.params.row.n + (0 + 0) + R.ecdsa.commitFuel)
          + (2 * R.sha.params.row.n
            + (0 + (R.sha.tape - ((2 * R.ecdsa.params.row.n + R.ecdsa.commitFuel)
              + (2 * R.sha.params.row.n + R.sha.commitFuel))))
            + R.sha.commitFuel) ≤ R.sha.tape ∧
      R.ecdsa.commitFuel < R.ecdsa.tape ∧ R.sha.commitFuel < R.sha.tape := by
  have hr := room h
  have ht := tape_eq h
  refine ⟨ht, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- **Both Reed–Solomon domains exist**, at any fields of the rows' cardinalities. -/
theorem domain_exists_ecdsa (h : R.Valid) {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = R.ecdsa.params.row.fieldSize) :
    Nonempty (LigeroFamily.ReedSolomon.Domain F R.ecdsa.params.row.openings R.ecdsa.params.q
      R.ecdsa.params.row.n) :=
  ⟨LigeroFamily.ReedSolomon.Domain.ofCardLE (by rw [hF]; exact rs_fits_ecdsa h)⟩

theorem domain_exists_sha (h : R.Valid) {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = R.sha.params.row.fieldSize) :
    Nonempty (LigeroFamily.ReedSolomon.Domain F R.sha.params.row.openings R.sha.params.q
      R.sha.params.row.n) :=
  ⟨LigeroFamily.ReedSolomon.Domain.ofCardLE (by rw [hF]; exact rs_fits_sha h)⟩

/-! ### Profile monotonicity -/

/-- The row at narrower profiles on both sides. -/
def withProfiles (R : TwoFieldRowV1) (P₁ P₂ : CostV1.Params) : TwoFieldRowV1 :=
  { R with ecdsa := { R.ecdsa with params := P₁ }, sha := { R.sha with params := P₂ } }

/--
**A valid two-field row covers every narrower pair of profiles.**  Each side by
`ProfileMonoV1.Row.valid_of_profile_le`; the shared-tape, two-field, room and domain conjuncts read
only fields `ProfileLe` holds fixed; the composed bound and size are sums of monotone terms.
-/
theorem valid_of_profile_le (h : R.Valid) {P₁ P₂ : CostV1.Params}
    (hle₁ : ProfileMonoV1.ProfileLe P₁ R.ecdsa.params) (hle₂ : ProfileMonoV1.ProfileLe P₂ R.sha.params)
    (hnl₁ : 0 < R.ecdsa.params.nl) (hnl₂ : 0 < R.sha.params.nl) :
    (R.withProfiles P₁ P₂).Valid := by
  obtain ⟨he, hs, ht, hd, ho₁, ho₂, hroom, hrs₁, hrs₂, hmac, hbound, hsize⟩ := h
  refine ⟨ProfileMonoV1.Row.valid_of_profile_le he hle₁ hnl₁,
    ProfileMonoV1.Row.valid_of_profile_le hs hle₂ hnl₂, ht, ?_, ?_, ?_, ?_, ?_, ?_, hmac, ?_, ?_⟩
  · show P₁.digestBits = P₂.digestBits
    rw [hle₁.digestBits, hle₂.digestBits]; exact hd
  · show P₁.row.fieldOrder ≠ 0
    rw [hle₁.row]; exact ho₁
  · show P₂.row.fieldOrder = 0
    rw [hle₂.row]; exact ho₂
  · show (2 * P₁.row.n + R.ecdsa.commitFuel) + (2 * P₂.row.n + R.sha.commitFuel) < R.sha.tape
    rw [hle₁.row, hle₂.row]; exact hroom
  · show P₁.row.openings + P₁.q + P₁.row.n ≤ P₁.row.fieldSize
    rw [hle₁.row, hle₁.q]; exact hrs₁
  · show P₂.row.openings + P₂.q + P₂.row.n ≤ P₂.row.fieldSize
    rw [hle₂.row, hle₂.q]; exact hrs₂
  · show ({ R.ecdsa with params := P₁ } : CertifiedV1.Row).bound
        + ({ R.sha with params := P₂ } : CertifiedV1.Row).bound + 1 / (R.macFieldSize : ℚ)
      ≤ 1 / 2 ^ R.lam
    have h₁ := ProfileMonoV1.Row.bound_le (R := R.ecdsa) hle₁
    have h₂ := ProfileMonoV1.Row.bound_le (R := R.sha) hle₂
    have : R.ecdsa.bound + R.sha.bound + 1 / (R.macFieldSize : ℚ) ≤ 1 / 2 ^ R.lam := hbound
    linarith
  · show P₁.proofBytes + P₂.proofBytes ≤ R.sizeBound
    have := ProfileMonoV1.proofBytes_le hle₁
    have := ProfileMonoV1.proofBytes_le hle₂
    omega

end TwoFieldRowV1

/-! ## The composed theorem at a valid row -/

section Compose

open Bcs Merkle Merkle.MH Merkle.RandomOracle
open scoped Classical
open LfzkV1.Mac LfzkV1.TwoField LfzkV1.TwoFieldBridge LfzkV1.TwoFieldV1

variable {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {D : Type} [Fintype D] [DecidableEq D] [Inhabited D]
variable {Fmac : Type} [Field Fmac] [Fintype Fmac] {nblk tlen T : ℕ}
variable {Cand₁ F₁ Equations₁ Witness₁ : Type} [Fintype Cand₁] [Nonempty Cand₁] [Field F₁]
  [Fintype F₁] [DecidableEq F₁] [SumcheckV1Interp F₁] [Fintype Equations₁] [DecidableEq Equations₁]
variable {nc₁ nv₁ logw₁ logc₁ : ℕ}
variable {Statement₁ Oracle₁ Challenge₁ Response₁ Query₁ : Type} {Opening₁ : Query₁ → Type}
variable {Enc₁ Salt₁ M₁ : Type} [DecidableEq Enc₁] [Inhabited Salt₁] [Inhabited M₁]
variable {Aux₁ Aux₁' : Type} {n₁ respondFuel₁ revealFuel₁ : ℕ}
variable {codec₁ : Codec Salt₁ M₁ D Enc₁} {dec₁ : RoleDecoders codec₁}
variable {K₁ : Compiler Statement₁ Oracle₁ Challenge₁ Response₁ Query₁ Opening₁ M₁ n₁}
variable {Cand₂ F₂ Equations₂ Witness₂ : Type} [Fintype Cand₂] [Nonempty Cand₂] [Field F₂]
  [Fintype F₂] [DecidableEq F₂] [SumcheckV1Interp F₂] [Fintype Equations₂] [DecidableEq Equations₂]
variable {nc₂ nv₂ logw₂ logc₂ : ℕ}
variable {Statement₂ Oracle₂ Challenge₂ Response₂ Query₂ : Type} {Opening₂ : Query₂ → Type}
variable {Enc₂ Salt₂ M₂ : Type} [DecidableEq Enc₂] [Inhabited Salt₂] [Inhabited M₂]
variable {Aux₂ Aux₂' : Type} {n₂ respondFuel₂ revealFuel₂ : ℕ}
variable {codec₂ : Codec Salt₂ M₂ D Enc₂} {dec₂ : RoleDecoders codec₂}
variable {K₂ : Compiler Statement₂ Oracle₂ Challenge₂ Response₂ Query₂ Opening₂ M₂ n₂}

/--
**A valid two-field V1 row certifies the composed protocol at `2^-lam`.**

`TwoFieldV1.twofield_v1_ratio_le_exact` at the row's two sides, with the MAC field of the row's size,
followed by the row's `target`.  The premises are the composed theorem's: per side a `V1Family` (see
`LfzkV1.TwoFieldV1` for exactly what it assumes), the MAC slot's data, and the MAC rows `hrow₁`,
`hrow₂`.
-/
theorem TwoFieldRowV1.nizk_ratio_le {R : TwoFieldRowV1} (h : R.Valid)
    (hFmac : Fintype.card Fmac = R.macFieldSize)
    (sch : Schedule (Rounds.Role.length R.ecdsa.params.nl R.ecdsa.params.rounds)
      (Rounds.Role.length R.sha.params.nl R.sha.params.rounds) T)
    {challengeOf₁ :
      (Fin (Rounds.Role.length R.ecdsa.params.nl R.ecdsa.params.rounds) → C) → Challenge₁}
    {queryOf₁ : (Fin (Rounds.Role.length R.ecdsa.params.nl R.ecdsa.params.rounds) → C) → Query₁}
    {dom₁ : LigeroFamily.ReedSolomon.Domain F₁ R.ecdsa.params.row.openings R.ecdsa.params.q
      R.ecdsa.params.row.n}
    {challengeOf₂ :
      (Fin (Rounds.Role.length R.sha.params.nl R.sha.params.rounds) → C) → Challenge₂}
    {queryOf₂ : (Fin (Rounds.Role.length R.sha.params.nl R.sha.params.rounds) → C) → Query₂}
    {dom₂ : LigeroFamily.ReedSolomon.Domain F₂ R.sha.params.row.openings R.sha.params.q
      R.sha.params.row.n}
    (L₁ : V1Family R.ecdsa (TwoFieldRowV1.ecdsa_valid h) (Rest sch.ι₁ → C) C Cand₁ F₁
      Equations₁ Witness₁ nc₁ nv₁ logw₁ logc₁ Aux₁ Aux₁' tlen n₁ respondFuel₁ revealFuel₁ dec₁ K₁
      challengeOf₁ queryOf₁ dom₁)
    (L₂ : V1Family R.sha (TwoFieldRowV1.sha_valid h) (Rest sch.ι₂ → C) C Cand₂ F₂
      Equations₂ Witness₂ nc₂ nv₂ logw₂ logc₂ Aux₂ Aux₂' tlen n₂ respondFuel₂ revealFuel₂ dec₂ K₂
      challengeOf₂ queryOf₂ dom₂)
    (decode : C → Fmac) (aP : (Fin tlen → D) → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    {keyB tag : (Fin tlen → D) × (Fin T → C) → Fin nblk → Fmac}
    (common₁ : Witness₁ → Fin nblk → Fmac)
    (hrow₁ : ∀ (ω : (Fin tlen → D) × (Fin T → C)) (cand : Cand₁),
      L₁.accepts (restOf sch.ι₁ ω.2) (ω.1, ω.2 ∘ sch.ι₁) → L₁.Sat (restOf sch.ι₁ ω.2) ω.1 cand →
      macTag (aP ω.1 + decode (ω.2 sch.s)) (keyB ω)
        (common₁ ((L₁.field (restOf sch.ι₁ ω.2) ω.1).wOf cand)) = tag ω)
    (common₂ : Witness₂ → Fin nblk → Fmac)
    (hrow₂ : ∀ (ω : (Fin tlen → D) × (Fin T → C)) (cand : Cand₂),
      L₂.accepts (restOf sch.ι₂ ω.2) (ω.1, ω.2 ∘ sch.ι₂) → L₂.Sat (restOf sch.ι₂ ω.2) ω.1 cand →
      macTag (aP ω.1 + decode (ω.2 sch.s)) (keyB ω)
        (common₂ ((L₂.field (restOf sch.ι₂ ω.2) ω.1).wOf cand)) = tag ω)
    (hT : 1 ≤ T) :
    ((univ.filter fun ω : (Fin tlen → D) × (Fin T → C) =>
        (L₁.macSide common₁ hrow₁).accepts ω ∧ (L₂.macSide common₂ hrow₂).accepts ω ∧
          composedE (L₁.macSide common₁ hrow₁) (L₂.macSide common₂ hrow₂) ω = none).card : ℚ)
        / (Fintype.card (Fin tlen → D) * (Fintype.card C : ℚ) ^ T)
      ≤ (1 : ℚ) / 2 ^ R.lam := by
  refine le_trans (twofield_v1_ratio_le_exact sch L₁ L₂ decode aP kmac hbal hmac common₁ hrow₁
    common₂ hrow₂ hT) ?_
  have ht := TwoFieldRowV1.target h
  unfold TwoFieldRowV1.bound at ht
  rw [hFmac]
  exact ht

end Compose

end LfzkV1.TwoFieldV1Rows
