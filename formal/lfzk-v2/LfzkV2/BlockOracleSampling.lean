import LfzkV2.ChallengeBlocks

/-!
# V2 challenge blocks on V1's adaptive oracle counter

Each hash point samples one complete block, including all output or assertion
coordinates. The full answer remains visible to the adversary. Only the local
block count is new; adaptive search and commitment-context handling are the
existing `Bcs.TotalOracle.CtxGrinding` theorem.
-/

namespace LfzkV2.FiatShamir

open Finset Merkle.RandomOracle Bcs.TotalOracle ChallengeBlocks
open scoped Classical

variable {F C Q Out Key Context Candidate : Type}
variable [Field F] [Fintype F] [DecidableEq F] [Fintype C] [DecidableEq Q]
variable [Fintype Candidate] {N L : ℕ}

structure BlockOracleSetup (F C : Type) [Field F] [Fintype F] [DecidableEq F] [Fintype C]
    (Q Out Key Context Candidate : Type) [DecidableEq Q] (N L : ℕ) where
  adversary : Tree Q C Out N
  hashInput : Out → ℕ → Q
  points : PrefixPoints Q
  key : Q → Key
  context : (Q → C) → Key → Context
  context_off : ∀ (H H' : Q → C) (x : Q), AgreeOff x H H' →
    context H' (key x) = context H (key x)
  kind : Q → Kind
  sampler : ∀ x, Sampler F C (kind x)
  unitFiber : ℕ
  balanced : unitFiber * Fintype.card F = Fintype.card C
  test : Context → (x : Q) → (Fin (points.slot x) → C) → Candidate → Data F (kind x)
  valid : ∀ ctx x pref candidate, Data.Valid (test ctx x pref candidate)

namespace BlockOracleSetup

variable (S : BlockOracleSetup F C Q Out Key Context Candidate N L)

theorem raw_bad_bound (ctx : Context) (x : Q) (pref : Fin (S.points.slot x) → C) :
    (univ.filter fun answer : C => ∃ candidate,
      Data.Bad (S.test ctx x pref candidate) ((S.sampler x).decode answer)).card ≤
        S.unitFiber * (Fintype.card Candidate * (S.kind x).budget) := by
  have heq : (univ.filter fun answer : C => ∃ candidate,
      Data.Bad (S.test ctx x pref candidate) ((S.sampler x).decode answer)) =
      univ.biUnion (fun candidate => univ.filter fun answer : C =>
        Data.Bad (S.test ctx x pref candidate) ((S.sampler x).decode answer)) := by
    ext answer
    simp
  rw [heq]
  calc
    _ ≤ ∑ candidate, (univ.filter fun answer : C =>
        Data.Bad (S.test ctx x pref candidate) ((S.sampler x).decode answer)).card := card_biUnion_le
    _ ≤ ∑ _ : Candidate, S.unitFiber * (S.kind x).budget := sum_le_sum fun candidate _ =>
      (S.sampler x).raw_bad_card S.unitFiber S.balanced _ (S.valid ctx x pref candidate)
    _ = _ := by simp; ring

noncomputable def grinding : CtxGrinding C Q Out Key Context N L where
  adversary := S.adversary
  hashInput := S.hashInput
  pts := S.points
  key := S.key
  ctxAt := S.context
  ctxAt_off := S.context_off
  Bad ctx x pref answer := ∃ candidate,
    Data.Bad (S.test ctx x pref candidate) ((S.sampler x).decode answer)
  beta x := S.unitFiber * (Fintype.card Candidate * (S.kind x).budget)
  bad_bound ctx x pref := by
    convert! S.raw_bad_bound ctx x pref using 1
    congr 1
    ext answer
    simp only [mem_filter]

/-- A complete decoded block costs its root budget per oracle query. In
particular, an assertion vector contributes one, rather than its length. -/
theorem soundness_le [Fintype Q] [Nonempty C]
    (maxBudget : ℕ) (hmax : ∀ x, (S.kind x).budget ≤ maxBudget)
    (slotBudget : Fin L → ℕ)
    (hslot : ∀ out i, (S.kind (S.hashInput out i.val)).budget ≤ slotBudget i)
    (event : (Q → C) → Prop)
    (hbad : ∀ H, event H → S.grinding.RoundBad H) :
    ((univ.filter event).card : ℚ) / (Fintype.card C : ℚ) ^ Fintype.card Q ≤
      (Fintype.card Candidate : ℚ) * (N*maxBudget + ∑ i, slotBudget i) / Fintype.card F := by
  have h := S.grinding.ratio_le (S.unitFiber * (Fintype.card Candidate * maxBudget))
    (fun x => Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (hmax x)))
    (fun i => S.unitFiber * (Fintype.card Candidate * slotBudget i))
    (fun out i => Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (hslot out i))) event hbad
  have hf : (0 : ℚ) < S.unitFiber := by
    have hc := Fintype.card_pos (α := C)
    have hb := S.balanced
    exact_mod_cast (show 0 < S.unitFiber by nlinarith)
  have hcard : (Fintype.card C : ℚ) = S.unitFiber * (Fintype.card F : ℚ) := by
    exact_mod_cast S.balanced.symm
  refine h.trans_eq ?_
  rw [hcard, ← Finset.mul_sum, ← Finset.mul_sum]
  push_cast
  field_simp [hf.ne']

end BlockOracleSetup
end LfzkV2.FiatShamir
