import LfzkV1.CostV1
import LfzkV1.LigeroV1LayerStep

/-!
# The certified table at Ligero V1

The certified table.  A `Row` bundles `LfzkV1.CostV1.Params` with a
security target, the list factor, the Merkle fuels and a size bound, and `Valid` checks, decidably:

1. the V1 row is valid (`LfzkV1.LigeroV1Rows.Row.Valid`: the certificate checks of
   `formal/ligero`, both doom thresholds, `epsRbr ≤ 2^-targetBits`, `d = n - k + 1`);
2. V1's witness layout, `r + q = k`, in place of V3's `dimension r q = k`;
3. `cardCand` is the row's own lift-list factor, `InterleavedJohnson.listBound`;
4. `CoreRowsNonempty nw nq`, the V1 theorem's well-formedness premise, at the cost model's rows;
5. the composed bound is at most `2^-lam`;
6. the modelled proof size is at most `sizeBound` bytes;
7. the hash tape has room for the compiler's leaves: `2·n + commitFuel < tape` at Ligero's `n`.
   Without it `hT` can force `n = 0`, which no compiler with a query has, and the theorem would be
   vacuous — as it is at the single-side and two-field V3 rows, which record `commitFuel = tape`
   (`LfzkV1.TwoFieldLongfellowRows.row_fuel_unsat`, from the two-field session);
8. the schedule is the zero-knowledge path's: `logc = 0`.  The bound charges `2·logw ly` sumcheck
   slots at layer `ly` (`CostV1.Params.rounds`), which is `Rounds`' schedule; `LfzkV1.API` and
   `LfzkV1.CoreSoundness` count `logc + 2·logw` rounds.  The two agree exactly at `logc = 0`
   (`Row.rounds_eq_api`), and `logc = 0` is what the ZK path asserts (`zk_common.h:L72`, README
   gap 5).  An earlier version recorded `logc := 16`, which neither the bound nor the size model
   reads, but which described a verifier with sixteen copy rounds per layer that the schedule does
   not have.

The V3 table's `ligero_budgets` conjunct compared numerals `blig, bquery` against `epsRbr`.  Here
the Ligero part of the bound *is* `cardCand · (fail + arith + cover)`, so `Row.ligero_budgets` is
an equation, `= epsRbr`, and the theorem below derives the two slot counts from the V1 theorem
instead of reading them off the row.

## The theorem

`Row.nizk_ratio_le`: at a valid row, for any Longfellow protocol instance whose Ligero step is V1
at the row's code, the compiled verifier accepts with extraction failing with probability at most
`2^-lam`.  Inside the statement:

* the Ligero half of LayerStep is **built** from `LigeroV1Rows.Row.rbr_soundness` at each failing
  commitment (`LigeroV1LayerStep.exists_ligeroData`): doom predicate, escaping set, `hesc`, query test,
  `hbq`;
* both Ligero slot counts are derived from the V1 densities through
  `Bcs.card_preimage_le_of_balanced` (`LigeroV1LayerStep.ligBudget_le`, `queryBudget_le`), and the
  field slots' from the decoders (`RbrSplit.FieldData.Exact.field_budgets`);
* the field rounds' budgets are `RbrLongfellow`'s theorems, as before.

**What is still a hypothesis**, and nothing else is:

* `hfalse` — at a commitment where extraction fails, the commitment's Ligero statement is false.
  Ligero's extractor; it is what the V1 theorem needs;
* `hfail` — extraction failure means no candidate satisfies the circuit;
* `hright` — the compiled verifier's acceptance, with extraction explaining it, implies LayerStep
  reaches `.accepted` at that commitment, where LayerStep's query test is the V1 verifier's
  (`LigeroV1LayerStep.accepting`).  This is README gap 1's transliteration debt, and it now includes
  that the IPCP prover `lig pre` answers as the compiled adversary does;
* `hexact` — the four coin decoders are exactly balanced (satisfiable:
  `RbrSplit.product_coins_exact`);
* the field half of LayerStep (`Ffam`): the layered circuit, the honest values and the boundary
  maps, with `RbrLongfellow`'s existing premises (`hzero0/1`, `hclaim`, `harith`, `Boundary.rel`,
  `Boundary.sound`);
* the protocol's ordinary premises: `|F| = 2^128`, a Reed–Solomon domain, the Merkle fuels.

Two modelling restrictions are inherited from LayerStep and stated rather than hidden: the Ligero
statement and its IPCP prover are fixed per commitment (LayerStep's doom at `.challenged x` reads
`x` only, so it cannot carry a statement that depends on the sumcheck prefix), and the
round-by-round notion is the sequential one (`LfzkV1.NizkMerkle`).

## Why the coin alphabet is not a row numeral

`LfzkV1.Certified`'s rows quote `cardC = 2^128` with `bpair = 1`.  `RbrSplit` proves that
`RbrLongfellow.LayerStepData` is empty below `bpair = 2|F|` over any non-empty coin space
(`LayerStepData.isEmpty_of_bpair_one`), so those rows' `nizk_ratio_le_longfellow` holds vacuously.  The
Ligero slots have the same problem in a stronger form: the V1 challenge space has far more than
`2^128` elements, so a `2^128` coin cannot be decoded onto it with the balance the density bound
needs.  `Row.nizk_ratio_le` therefore holds for **every** coin alphabet with exactly balanced
decoders, and the bound it quotes is per field element.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LfzkV1.CertifiedV1

open Finset

/-- One certified parameter row at a V1 Ligero row. -/
structure Row where
  params : LfzkV1.CostV1.Params
  /-- The security target, in bits. -/
  lam : ℕ
  /-- Candidate count — the lift-list size. -/
  cardCand : ℕ
  commitFuel : ℕ
  /-- Hash-tape length. -/
  tape : ℕ
  /-- Modelled proof size, in bytes. -/
  sizeBound : ℕ

namespace Row

variable (R : Row)

/-- The composed bound at this row's numerals. -/
def bound : ℚ := R.params.nizkBound R.cardCand R.commitFuel R.tape

/-- A checked row; see the module docstring for the eight conjuncts. -/
def Valid : Prop :=
  R.params.row.Valid ∧
    R.params.row.openings + R.params.q = R.params.row.k ∧
    R.cardCand = R.params.row.listBound ∧
    LigeroFamily.CoreRowsNonempty R.params.nw R.params.nq ∧
    R.bound ≤ (1 : ℚ) / 2 ^ R.lam ∧
    R.params.proofBytes ≤ R.sizeBound ∧
    2 * R.params.row.n + R.commitFuel < R.tape ∧
    R.params.logc = 0

instance : Decidable R.Valid := by
  unfold Valid LigeroFamily.CoreRowsNonempty
  infer_instance

def validBool : Bool := decide R.Valid

/-- The recorded `lam` is the bound's exact integer bit level: one more bit fails. -/
def Sharp : Prop := ¬ R.bound ≤ (1 : ℚ) / 2 ^ (R.lam + 1)

instance : Decidable R.Sharp := by unfold Sharp; infer_instance

def sharpBool : Bool := decide R.Sharp

variable {R}

theorem valid_of_validBool (h : R.validBool = true) : R.Valid := of_decide_eq_true h

theorem rowValid (h : R.Valid) : R.params.row.Valid := h.1

/-- **V1's witness layout**, `r + w = k`. -/
theorem hkrow (h : R.Valid) : R.params.row.openings + R.params.q = R.params.row.k := h.2.1

/-- The lift-list factor is the V1 row's own. -/
theorem cand_eq (h : R.Valid) : R.cardCand = R.params.row.listBound := h.2.2.1

theorem coreRows (h : R.Valid) : LigeroFamily.CoreRowsNonempty R.params.nw R.params.nq :=
  h.2.2.2.1

theorem target (h : R.Valid) : R.bound ≤ (1 : ℚ) / 2 ^ R.lam := h.2.2.2.2.1

theorem size (h : R.Valid) : R.params.proofBytes ≤ R.sizeBound := h.2.2.2.2.2.1

/-- **The tape has room for the compiler's leaves.**  `Row.nizk_ratio_le` takes
`hT : 2·n + (revealFuel + respondFuel) + commitFuel ≤ tape`, and a compiler with a query has
`n ≥ 1` leaves (`K.indices_nonempty`), so `tape = commitFuel` would make `hT` unsatisfiable and the
theorem vacuous.  This conjunct rules that out at `n = row.n`, Ligero's column count. -/
theorem fuel_room (h : R.Valid) : 2 * R.params.row.n + R.commitFuel < R.tape :=
  h.2.2.2.2.2.2.1

/-- **The zero-knowledge schedule.**  No copy rounds: `zk_common.h:L72` asserts `logc == 0`. -/
theorem logc_eq (h : R.Valid) : R.params.logc = 0 := h.2.2.2.2.2.2.2

/-- **The bound's round count is `API`'s.**  `CostV1.Params.rounds ly = 2·logw ly` is the schedule
the bound charges and LayerStep runs; `LfzkV1.API`/`LfzkV1.CoreSoundness` count `logc + 2·logw` rounds
per layer.  At a valid row they are the same number. -/
theorem rounds_eq_api (h : R.Valid) (ly : ℕ) :
    R.params.rounds ly = R.params.logc + 2 * R.params.logw ly := by
  rw [logc_eq h, Nat.zero_add]
  rfl

/-- `hT` is satisfiable at the row: at `n = row.n` columns, with the rest of the tape as the
adversary's opening fuel. -/
theorem hT_satisfiable (h : R.Valid) :
    2 * R.params.row.n + (0 + (R.tape - (2 * R.params.row.n + R.commitFuel))) + R.commitFuel
      ≤ R.tape := by
  have := fuel_room h
  omega

/--
**The two Ligero budgets are the V1 row's.**  The Ligero part of the composed bound,
`cardCand · ((fail + arith) + cover)`, is exactly the row's `epsRbr`, which `LigeroV1Rows`
certifies at `2^-targetBits`.
-/
theorem ligero_budgets (h : R.Valid) :
    (R.cardCand : ℚ) * R.params.ligeroDensity = R.params.row.epsRbr ∧
      R.params.row.epsRbr ≤ (1 : ℚ) / 2 ^ R.params.row.targetBits := by
  refine ⟨?_, ?_⟩
  · rw [cand_eq h]
    exact R.params.ligero_part_eq_epsRbr
  · simpa [LfzkV1.LigeroV1Rows.Row.epsRbr, add_assoc] using
      LfzkV1.LigeroV1Rows.Row.eps_le_target (rowValid h)

end Row

section Compose

open Bcs Merkle Merkle.MH Merkle.RandomOracle RbrLongfellow
open scoped Classical

/-- The field slots' budget, `⌊2|C|/|F|⌋`. -/
def pairBudget (cardC cardF : ℕ) : ℕ := 2 * cardC / cardF

/-- The input binding's budget, `⌊|C|/|F|⌋`. -/
def inBudget (cardC cardF : ℕ) : ℕ := cardC / cardF

/-- The Ligero challenge slot's budget, `⌊(fail + arith) · |C|⌋`. -/
def ligBudget (row : LfzkV1.LigeroV1Rows.Row) (cardC : ℕ) : ℕ :=
  ⌊(row.fail + row.arith) * cardC⌋₊

/-- The Ligero query slot's budget, `⌊cover · |C|⌋`. -/
def queryBudget (row : LfzkV1.LigeroV1Rows.Row) (cardC : ℕ) : ℕ :=
  ⌊row.cover * cardC⌋₊

/--
**The budgets, in densities.**  At `|C| > 0` and `|F| = row.fieldSize > 0`, LayerStep's class
budgets over `|C|` are at most `nizkBound`'s densities, so `nizk_ratio_le_merkle`'s right-hand side
is at most `Row.bound`.
-/
theorem budgets_le_bound (R : Row) {cardC cardCand cardD : ℕ} (hC : 0 < cardC)
    (hF : 0 < R.params.row.fieldSize) (hD : cardD = 2 ^ R.params.digestBits) :
    ((cardCand * (R.params.nl * pairBudget cardC R.params.row.fieldSize
          + (∑ i ∈ Finset.range R.params.nl, R.params.rounds i)
            * pairBudget cardC R.params.row.fieldSize
          + inBudget cardC R.params.row.fieldSize + ligBudget R.params.row cardC
          + queryBudget R.params.row cardC) : ℕ) : ℚ) / (cardC : ℚ)
        + (merkleNumerator R.commitFuel R.tape : ℚ) / (cardD : ℚ)
      ≤ R.params.nizkBound cardCand R.commitFuel R.tape := by
  have hc : (0 : ℚ) < (cardC : ℚ) := by exact_mod_cast hC
  have hf : (0 : ℚ) < (R.params.row.fieldSize : ℚ) := by exact_mod_cast hF
  set f : ℚ := (R.params.row.fieldSize : ℚ)
  set c : ℚ := (cardC : ℚ)
  have hfa := add_nonneg (LigeroV1LayerStep.fail_nonneg R.params.row)
    (LigeroV1LayerStep.arith_nonneg R.params.row)
  have hcv := LigeroV1LayerStep.cover_nonneg R.params.row
  -- each budget is at most its density times `|C|`
  have hbp : (pairBudget cardC R.params.row.fieldSize : ℚ) ≤ c * (2 / f) := by
    unfold pairBudget
    refine le_trans (Nat.cast_div_le) (le_of_eq ?_)
    push_cast
    ring
  have hbi : (inBudget cardC R.params.row.fieldSize : ℚ) ≤ c * (1 / f) := by
    unfold inBudget
    refine le_trans (Nat.cast_div_le) (le_of_eq ?_)
    ring
  have hbl : (ligBudget R.params.row cardC : ℚ) ≤ c * (R.params.row.fail + R.params.row.arith) := by
    unfold ligBudget
    refine le_trans (Nat.floor_le (mul_nonneg hfa (Nat.cast_nonneg _))) (le_of_eq ?_)
    ring
  have hbq : (queryBudget R.params.row cardC : ℚ) ≤ c * R.params.row.cover := by
    unfold queryBudget
    refine le_trans (Nat.floor_le (mul_nonneg hcv (Nat.cast_nonneg _))) (le_of_eq ?_)
    ring
  have hS : (∑ i ∈ Finset.range R.params.nl, R.params.rounds i) = R.params.totalRounds := rfl
  have hinner :
      ((R.params.nl * pairBudget cardC R.params.row.fieldSize
          + (∑ i ∈ Finset.range R.params.nl, R.params.rounds i)
            * pairBudget cardC R.params.row.fieldSize
          + inBudget cardC R.params.row.fieldSize + ligBudget R.params.row cardC
          + queryBudget R.params.row cardC : ℕ) : ℚ)
        ≤ c * (R.params.fieldDensity + R.params.ligeroDensity) := by
    rw [hS]
    push_cast
    have h1 : (R.params.nl : ℚ) * (pairBudget cardC R.params.row.fieldSize : ℚ)
        ≤ (R.params.nl : ℚ) * (c * (2 / f)) :=
      mul_le_mul_of_nonneg_left hbp (Nat.cast_nonneg _)
    have h2 : (R.params.totalRounds : ℚ) * (pairBudget cardC R.params.row.fieldSize : ℚ)
        ≤ (R.params.totalRounds : ℚ) * (c * (2 / f)) :=
      mul_le_mul_of_nonneg_left hbp (Nat.cast_nonneg _)
    have hrhs : c * (R.params.fieldDensity + R.params.ligeroDensity)
        = (R.params.nl : ℚ) * (c * (2 / f)) + (R.params.totalRounds : ℚ) * (c * (2 / f))
          + c * (1 / f) + c * (R.params.row.fail + R.params.row.arith)
          + c * R.params.row.cover := by
      unfold LfzkV1.CostV1.Params.fieldDensity LfzkV1.CostV1.Params.ligeroDensity
      push_cast
      field_simp
      ring
    rw [hrhs]
    linarith
  have hmerkle : (merkleNumerator R.commitFuel R.tape : ℚ) / (cardD : ℚ)
      = R.params.merkleTerm R.commitFuel R.tape := by
    unfold LfzkV1.CostV1.Params.merkleTerm
    rw [hD]
    push_cast
    rfl
  unfold LfzkV1.CostV1.Params.nizkBound
  rw [hmerkle]
  refine add_le_add ?_ le_rfl
  rw [div_le_iff₀ hc, Nat.cast_mul]
  calc (cardCand : ℚ) * ((R.params.nl * pairBudget cardC R.params.row.fieldSize
          + (∑ i ∈ Finset.range R.params.nl, R.params.rounds i)
            * pairBudget cardC R.params.row.fieldSize
          + inBudget cardC R.params.row.fieldSize + ligBudget R.params.row cardC
          + queryBudget R.params.row cardC : ℕ) : ℚ)
      ≤ (cardCand : ℚ) * (c * (R.params.fieldDensity + R.params.ligeroDensity)) :=
        mul_le_mul_of_nonneg_left hinner (Nat.cast_nonneg _)
    _ = (cardCand : ℚ) * (R.params.fieldDensity + R.params.ligeroDensity) * c := by ring

/--
**A certified V1 row certifies the protocol at its exact bound**, with the honest values and the
satisfaction predicate allowed to depend on the commitment.

The right-hand side is `Row.bound`, the rational the row's `Valid` compares against `2^-lam`, rather
than `2^-lam` itself: a two-field composition adds two sides' bounds and the MAC term before
comparing, so it needs each side's exact bound (`LfzkV1.TwoFieldV1`).  `Row.nizk_ratio_le_family` is
this followed by `Row.target`.
-/
theorem Row.nizk_ratio_le_family_bound {R : Row} (h : R.Valid)
    {C Cand : Type} [Fintype C] [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand]
    {F Equations Witness : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckV1Interp F]
    [Fintype Equations] [DecidableEq Equations]
    {logw logc nc nv : ℕ}
    {Statement Oracle Challenge Response Query : Type} {Opening : Query → Type}
    {Enc D Salt M Aux Aux' : Type} {n respondFuel revealFuel : ℕ}
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt] [Inhabited M]
    {codec : Codec Salt M D Enc} (dec : RoleDecoders codec)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (A : Adversary Enc D Salt M Challenge Response Query Aux Aux'
      n R.commitFuel respondFuel revealFuel)
    (challengeOf : (Fin (Rounds.Role.length R.params.nl R.params.rounds) → C) → Challenge)
    (queryOf : (Fin (Rounds.Role.length R.params.nl R.params.rounds) → C) → Query)
    (statement : (Fin R.tape → D) ×
      (Fin (Rounds.Role.length R.params.nl R.params.rounds) → C) → Statement)
    {Fails : (Fin R.tape → D) → Prop}
    -- the Ligero V1 step: the field, the code's domain, and one instance per commitment
    (hF : Fintype.card F = R.params.row.fieldSize)
    (dom : LigeroFamily.ReedSolomon.Domain F R.params.row.openings R.params.q R.params.row.n)
    (lig : ∀ _pre : Fin R.tape → D,
      LigeroV1LayerStep.Instance R.params.row F Equations R.params.nw R.params.nq R.params.q)
    (hfalse : ∀ pre : Fin R.tape → D, Fails pre → ¬ (lig pre).statement.Language)
    -- the field half of LayerStep, one per commitment, with exactly balanced decoders
    (H : ∀ _pre : Fin R.tape → D, RbrLongfellow.Honest F Cand logw logc)
    (Sat : (Fin R.tape → D) → Cand → Prop)
    (Ffam : ∀ pre : Fin R.tape → D,
      RbrSplit.FieldData C F (LigeroV1LayerStep.Chal F Equations R.params.nw R.params.nq)
        (LigeroV1LayerStep.Qry R.params.row) Cand Witness nc nv logw logc (H pre) (Sat pre))
    (hexact : ∀ pre : Fin R.tape → D, (Ffam pre).Exact)
    -- extraction, and acceptance
    (hfail : ∀ pre : Fin R.tape → D, Fails pre → ∀ cand : Cand, ¬ Sat pre cand)
    (hright : ∀ pre : Fin R.tape → D, Fails pre →
      ∀ tape : Fin (Rounds.Role.length R.params.nl R.params.rounds) → C,
        (CompiledAccepts K A codec (statement (pre, tape))
            (challengeOf tape) (queryOf tape) pre ∧
          ExtractionExplains codec dec n R.commitFuel (revealFuel + respondFuel) R.tape
            A.commit (A.openingStage (challengeOf tape) (queryOf tape)) pre) →
        RbrSplit.LayerStepAccepts
          (RbrSplit.stepsOf (nl := R.params.nl) (w := R.params.rounds) (Ffam pre)
            (fun _ _ => LigeroV1LayerStep.accepting (Row.rowValid h) dom (Row.hkrow h) (lig pre)))
          tape)
    -- the Merkle extractor's fuels
    (ht₁ : R.commitFuel ≤ R.tape)
    (hT : 2 * n + (revealFuel + respondFuel) + R.commitFuel ≤ R.tape) (hT1 : 1 ≤ R.tape)
    (hcand : Fintype.card Cand = R.cardCand)
    (hD : Fintype.card D = 2 ^ R.params.digestBits) :
    ((univ.filter fun omega : (Fin R.tape → D) ×
          (Fin (Rounds.Role.length R.params.nl R.params.rounds) → C) =>
        CompiledAccepts K A codec (statement omega)
            (challengeOf omega.2) (queryOf omega.2) omega.1 ∧ Fails omega.1).card : ℚ)
        / (Fintype.card (Fin R.tape → D) *
            (Fintype.card C : ℚ) ^ Rounds.Role.length R.params.nl R.params.rounds)
      ≤ R.bound := by
  classical
  -- the Ligero half, at each commitment where extraction fails
  have hex := fun (pre : Fin R.tape → D) (hFp : Fails pre) =>
    LigeroV1LayerStep.exists_ligeroData C (Row.rowValid h) (Row.coreRows h) hF dom (Row.hkrow h)
      (lig pre) (hfalse pre hFp)
  choose LigD LD hacc hesc hbq using hex
  -- the five class budgets, relative to `|C|`
  have hFpos : 0 < R.params.row.fieldSize := by rw [← hF]; exact Fintype.card_pos
  have hCpos : 0 < Fintype.card C := Fintype.card_pos
  have ep : 2 * Fintype.card C / Fintype.card F
      = pairBudget (Fintype.card C) R.params.row.fieldSize := by rw [hF]; rfl
  have ei : Fintype.card C / Fintype.card F
      = inBudget (Fintype.card C) R.params.row.fieldSize := by rw [hF]; rfl
  have hB : ∀ (pre : Fin R.tape → D) (hFp : Fails pre),
      RbrSplit.Budgets (Ffam pre) (LD pre hFp)
        (pairBudget (Fintype.card C) R.params.row.fieldSize)
        (pairBudget (Fintype.card C) R.params.row.fieldSize)
        (inBudget (Fintype.card C) R.params.row.fieldSize)
        (ligBudget R.params.row (Fintype.card C)) (queryBudget R.params.row (Fintype.card C)) := by
    intro pre hFp
    obtain ⟨hp0, hp1, hr, hi⟩ := (hexact pre).field_budgets
    obtain ⟨-, -, hchal, hq⟩ := hexact pre
    exact ⟨hp0.trans_eq ep, hp1.trans_eq ep, hr.trans_eq ep, hi.trans_eq ei,
      LigeroV1LayerStep.ligBudget_le (hesc pre hFp) hchal,
      (hbq pre hFp) ▸ LigeroV1LayerStep.queryBudget_le hq⟩
  -- acceptance at the built Ligero half
  have hright' : ∀ (pre : Fin R.tape → D) (hFp : Fails pre),
      RightOfAccepts (H := H pre) (Sat pre) (LigD pre hFp)
        (RbrSplit.steps (nl := R.params.nl) (w := R.params.rounds) (Ffam pre) (LD pre hFp))
        (fun tape =>
          CompiledAccepts K A codec (statement (pre, tape))
              (challengeOf tape) (queryOf tape) pre ∧
            ExtractionExplains codec dec n R.commitFuel (revealFuel + respondFuel) R.tape
              A.commit (A.openingStage (challengeOf tape) (queryOf tape)) pre) := by
    intro pre hFp
    refine RbrSplit.rightOfAccepts_of_layerStepAccepts _ fun tape hacc' => ?_
    show RbrSplit.LayerStepAccepts (RbrSplit.stepsOf (Ffam pre) (LD pre hFp).accepting) tape
    rw [hacc pre hFp]
    exact hright pre hFp tape hacc'
  -- the round-by-round family: LayerStep where extraction fails, the trivial object elsewhere
  let beta : Fin (Rounds.Role.length R.params.nl R.params.rounds) → ℕ := fun i =>
    Fintype.card Cand * RbrLayerStep.classBudget (nl := R.params.nl) (w := R.params.rounds)
      (pairBudget (Fintype.card C) R.params.row.fieldSize)
      (pairBudget (Fintype.card C) R.params.row.fieldSize)
      (inBudget (Fintype.card C) R.params.row.fieldSize) (ligBudget R.params.row (Fintype.card C))
      (queryBudget R.params.row (Fintype.card C)) (Rounds.Role.indexEquiv.symm i)
  let Rfam : ∀ pre : Fin R.tape → D, Bcs.Rbr C (Rounds.Role.length R.params.nl R.params.rounds)
      (fun tape =>
        CompiledAccepts K A codec (statement (pre, tape))
            (challengeOf tape) (queryOf tape) pre ∧
          ExtractionExplains codec dec n R.commitFuel (revealFuel + respondFuel) R.tape
            A.commit (A.openingStage (challengeOf tape) (queryOf tape)) pre)
      (Fails pre) := fun pre =>
    if hFp : Fails pre then
      (Ffam pre).rbr (LD pre hFp) (hB pre hFp) (hfail pre) (hright' pre hFp)
    else RbrSplit.trivialRbr hFp beta
  have hbeta : ∀ (pre : Fin R.tape → D) (i : Fin (Rounds.Role.length R.params.nl R.params.rounds)),
      (Rfam pre).beta i ≤ beta i := by
    intro pre i
    by_cases hFp : Fails pre
    · simp only [Rfam, dif_pos hFp]
      exact le_rfl
    · simp only [Rfam, dif_neg hFp]
      exact le_rfl
  have hlen : 1 ≤ Rounds.Role.length R.params.nl R.params.rounds := by
    show 1 ≤ Rounds.Role.layerBase R.params.rounds R.params.nl + 3
    omega
  have hmain := LfzkV1.Nizk.nizk_ratio_le_merkle (Cand := Cand) dec K A challengeOf queryOf
    statement Rfam (pairBudget (Fintype.card C) R.params.row.fieldSize)
    (pairBudget (Fintype.card C) R.params.row.fieldSize)
    (inBudget (Fintype.card C) R.params.row.fieldSize)
    (ligBudget R.params.row (Fintype.card C)) (queryBudget R.params.row (Fintype.card C))
    hbeta hlen ht₁ hT hT1
  refine le_trans hmain ?_
  rw [hcand]
  exact budgets_le_bound R hCpos hFpos hD

/--
**A certified V1 row certifies the protocol**, with the honest values and the satisfaction
predicate allowed to depend on the commitment.

`Row.nizk_ratio_le` is the case where they do not.  A two-field side needs this form: its statement
includes the MAC key, which is a function of the commitment, so its `H` and `Sat` are too.  The list
factor `|Cand|` stays uniform, because the bound charges it once.
-/
theorem Row.nizk_ratio_le_family {R : Row} (h : R.Valid)
    {C Cand : Type} [Fintype C] [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand]
    {F Equations Witness : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckV1Interp F]
    [Fintype Equations] [DecidableEq Equations]
    {logw logc nc nv : ℕ}
    {Statement Oracle Challenge Response Query : Type} {Opening : Query → Type}
    {Enc D Salt M Aux Aux' : Type} {n respondFuel revealFuel : ℕ}
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt] [Inhabited M]
    {codec : Codec Salt M D Enc} (dec : RoleDecoders codec)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (A : Adversary Enc D Salt M Challenge Response Query Aux Aux'
      n R.commitFuel respondFuel revealFuel)
    (challengeOf : (Fin (Rounds.Role.length R.params.nl R.params.rounds) → C) → Challenge)
    (queryOf : (Fin (Rounds.Role.length R.params.nl R.params.rounds) → C) → Query)
    (statement : (Fin R.tape → D) ×
      (Fin (Rounds.Role.length R.params.nl R.params.rounds) → C) → Statement)
    {Fails : (Fin R.tape → D) → Prop}
    -- the Ligero V1 step: the field, the code's domain, and one instance per commitment
    (hF : Fintype.card F = R.params.row.fieldSize)
    (dom : LigeroFamily.ReedSolomon.Domain F R.params.row.openings R.params.q R.params.row.n)
    (lig : ∀ _pre : Fin R.tape → D,
      LigeroV1LayerStep.Instance R.params.row F Equations R.params.nw R.params.nq R.params.q)
    (hfalse : ∀ pre : Fin R.tape → D, Fails pre → ¬ (lig pre).statement.Language)
    -- the field half of LayerStep, one per commitment, with exactly balanced decoders
    (H : ∀ _pre : Fin R.tape → D, RbrLongfellow.Honest F Cand logw logc)
    (Sat : (Fin R.tape → D) → Cand → Prop)
    (Ffam : ∀ pre : Fin R.tape → D,
      RbrSplit.FieldData C F (LigeroV1LayerStep.Chal F Equations R.params.nw R.params.nq)
        (LigeroV1LayerStep.Qry R.params.row) Cand Witness nc nv logw logc (H pre) (Sat pre))
    (hexact : ∀ pre : Fin R.tape → D, (Ffam pre).Exact)
    -- extraction, and acceptance
    (hfail : ∀ pre : Fin R.tape → D, Fails pre → ∀ cand : Cand, ¬ Sat pre cand)
    (hright : ∀ pre : Fin R.tape → D, Fails pre →
      ∀ tape : Fin (Rounds.Role.length R.params.nl R.params.rounds) → C,
        (CompiledAccepts K A codec (statement (pre, tape))
            (challengeOf tape) (queryOf tape) pre ∧
          ExtractionExplains codec dec n R.commitFuel (revealFuel + respondFuel) R.tape
            A.commit (A.openingStage (challengeOf tape) (queryOf tape)) pre) →
        RbrSplit.LayerStepAccepts
          (RbrSplit.stepsOf (nl := R.params.nl) (w := R.params.rounds) (Ffam pre)
            (fun _ _ => LigeroV1LayerStep.accepting (Row.rowValid h) dom (Row.hkrow h) (lig pre)))
          tape)
    -- the Merkle extractor's fuels
    (ht₁ : R.commitFuel ≤ R.tape)
    (hT : 2 * n + (revealFuel + respondFuel) + R.commitFuel ≤ R.tape) (hT1 : 1 ≤ R.tape)
    (hcand : Fintype.card Cand = R.cardCand)
    (hD : Fintype.card D = 2 ^ R.params.digestBits) :
    ((univ.filter fun omega : (Fin R.tape → D) ×
          (Fin (Rounds.Role.length R.params.nl R.params.rounds) → C) =>
        CompiledAccepts K A codec (statement omega)
            (challengeOf omega.2) (queryOf omega.2) omega.1 ∧ Fails omega.1).card : ℚ)
        / (Fintype.card (Fin R.tape → D) *
            (Fintype.card C : ℚ) ^ Rounds.Role.length R.params.nl R.params.rounds)
      ≤ (1 : ℚ) / 2 ^ R.lam :=
  le_trans (Row.nizk_ratio_le_family_bound h dec K A challengeOf queryOf statement hF dom lig
    hfalse H Sat Ffam hexact hfail hright ht₁ hT hT1 hcand hD) (Row.target h)


/--
**A certified V1 row certifies the protocol.**

At any Longfellow protocol instance over the row's parameters whose Ligero step is V1 at the row's
Reed–Solomon code, the compiled verifier accepts while extraction fails with probability at most
`2^-lam`.  The Ligero half of LayerStep is built from `RbrCertifiedV1.Row.rbr_soundness` inside the
proof; see the module docstring for exactly which premises remain.
-/
theorem Row.nizk_ratio_le {R : Row} (h : R.Valid)
    {C Cand : Type} [Fintype C] [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand]
    {F Equations Witness : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckV1Interp F]
    [Fintype Equations] [DecidableEq Equations]
    {logw logc nc nv : ℕ}
    {H : RbrLongfellow.Honest F Cand logw logc} {Sat : Cand → Prop}
    {Statement Oracle Challenge Response Query : Type} {Opening : Query → Type}
    {Enc D Salt M Aux Aux' : Type} {n respondFuel revealFuel : ℕ}
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt] [Inhabited M]
    {codec : Codec Salt M D Enc} (dec : RoleDecoders codec)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (A : Adversary Enc D Salt M Challenge Response Query Aux Aux'
      n R.commitFuel respondFuel revealFuel)
    (challengeOf : (Fin (Rounds.Role.length R.params.nl R.params.rounds) → C) → Challenge)
    (queryOf : (Fin (Rounds.Role.length R.params.nl R.params.rounds) → C) → Query)
    (statement : (Fin R.tape → D) ×
      (Fin (Rounds.Role.length R.params.nl R.params.rounds) → C) → Statement)
    {Fails : (Fin R.tape → D) → Prop}
    -- the Ligero V1 step: the field, the code's domain, and one instance per commitment
    (hF : Fintype.card F = R.params.row.fieldSize)
    (dom : LigeroFamily.ReedSolomon.Domain F R.params.row.openings R.params.q R.params.row.n)
    (lig : ∀ _pre : Fin R.tape → D,
      LigeroV1LayerStep.Instance R.params.row F Equations R.params.nw R.params.nq R.params.q)
    (hfalse : ∀ pre : Fin R.tape → D, Fails pre → ¬ (lig pre).statement.Language)
    -- the field half of LayerStep, one per commitment, with exactly balanced decoders
    (Ffam : ∀ _pre : Fin R.tape → D,
      RbrSplit.FieldData C F (LigeroV1LayerStep.Chal F Equations R.params.nw R.params.nq)
        (LigeroV1LayerStep.Qry R.params.row) Cand Witness nc nv logw logc H Sat)
    (hexact : ∀ pre : Fin R.tape → D, (Ffam pre).Exact)
    -- extraction, and acceptance
    (hfail : ∀ pre : Fin R.tape → D, Fails pre → ∀ cand : Cand, ¬ Sat cand)
    (hright : ∀ pre : Fin R.tape → D, Fails pre →
      ∀ tape : Fin (Rounds.Role.length R.params.nl R.params.rounds) → C,
        (CompiledAccepts K A codec (statement (pre, tape))
            (challengeOf tape) (queryOf tape) pre ∧
          ExtractionExplains codec dec n R.commitFuel (revealFuel + respondFuel) R.tape
            A.commit (A.openingStage (challengeOf tape) (queryOf tape)) pre) →
        RbrSplit.LayerStepAccepts
          (RbrSplit.stepsOf (nl := R.params.nl) (w := R.params.rounds) (Ffam pre)
            (fun _ _ => LigeroV1LayerStep.accepting (Row.rowValid h) dom (Row.hkrow h) (lig pre)))
          tape)
    -- the Merkle extractor's fuels
    (ht₁ : R.commitFuel ≤ R.tape)
    (hT : 2 * n + (revealFuel + respondFuel) + R.commitFuel ≤ R.tape) (hT1 : 1 ≤ R.tape)
    (hcand : Fintype.card Cand = R.cardCand)
    (hD : Fintype.card D = 2 ^ R.params.digestBits) :
    ((univ.filter fun omega : (Fin R.tape → D) ×
          (Fin (Rounds.Role.length R.params.nl R.params.rounds) → C) =>
        CompiledAccepts K A codec (statement omega)
            (challengeOf omega.2) (queryOf omega.2) omega.1 ∧ Fails omega.1).card : ℚ)
        / (Fintype.card (Fin R.tape → D) *
            (Fintype.card C : ℚ) ^ Rounds.Role.length R.params.nl R.params.rounds)
      ≤ (1 : ℚ) / 2 ^ R.lam :=
  Row.nizk_ratio_le_family h dec K A challengeOf queryOf statement hF dom lig hfalse
    (fun _ => H) (fun _ => Sat) Ffam hexact hfail hright ht₁ hT hT1 hcand hD

end Compose

end LfzkV1.CertifiedV1
