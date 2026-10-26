import Merkle.ChildHits
import Mathlib.Algebra.Order.Field.Rat

/-! Merkle acceptance with fewer queries than an authentication path needs.
An accepted opening either contains an input absent from the prover's
queries, or the prover guessed a child digest before obtaining its hash.
Both cases have a digest-size denominator. -/

namespace Merkle.MH

open Finset RandomOracle
open scoped Classical

variable {Salt M D Enc Out Result : Type}
variable [Inhabited D] [DecidableEq Enc] [Fintype D] [DecidableEq D]
variable {n budget TM fuel : ℕ}
variable (codec : Codec Salt M D Enc) (dec : RoleDecoders codec)
variable (commit : Tree Enc D Out budget) (rootOf : Out → D)
variable (claimOf : Out → OpeningClaim n Salt M D)
variable (R : Tree Enc D Result fuel)
variable (hbudget : budget < 8) (hn : 128 ≤ n) (ht : budget ≤ TM) (hF : fuel ≤ TM)
variable (hpref : ∀ tape : Fin TM → D,
  (lazyRun tape default commit []).2.1 <+: runSlots TM R tape)
variable (hcheck : ∀ tape : Fin TM → D,
  let cl := claimOf (lazyRun tape default commit []).1
  ∀ qa ∈ ((checkPass codec n cl.I cl.a cl.pf (2*n) fun _ => default).run
    (runOracle TM R tape)).2, qa ∈ (R.run (runOracle TM R tape)).2)

noncomputable def smallBudgetAccepts (tape : Fin TM → D) : Prop :=
  let out := (lazyRun tape default commit []).1
  let cl := claimOf out
  Accepts (codec.withOracle (runOracle TM R tape)) n (rootOf out) cl.I cl.a cl.pf

include dec hbudget hn ht hF hpref hcheck

theorem smallBudget_acceptance_card_le :
    (univ.filter (smallBudgetAccepts (TM := TM) codec commit rootOf claimOf R)).card ≤
      (2*budget*budget + fuel*(2*budget+1))*Fintype.card D^(TM-1) := by
  let first := ChildHit dec commit ht
  let second := HitFamily TM (extractionHits fuel budget)
    (fun p => (⟨p.1.val,lt_of_lt_of_le p.1.isLt hF⟩ : Fin TM))
    (fun p => hitTargetOf codec dec budget TM commit rootOf
      ⟨p.1.val,lt_of_lt_of_le p.1.isLt hF⟩ p.2)
  have hcover (tape : Fin TM → D)
      (hacc : smallBudgetAccepts codec commit rootOf claimOf R tape) :
      first tape ∨ second tape := by
    by_cases hhit : first tape
    · exact Or.inl hhit
    · right
      let out := (lazyRun tape default commit []).1
      let cl := claimOf out
      let H := runOracle TM R tape
      let seen := (lazyRun tape default commit []).2.1
      have hans q (hq : q ∈ seen) : H q = tapeAt tape default (seen.idxOf q) := by
        obtain ⟨rest,he⟩ := hpref tape
        change tapeAt tape default ((runSlots TM R tape).idxOf q) = _
        rw [← he,List.idxOf_append_of_mem hq]
      have hbefore := childrenEarlier_of_not_childHit dec commit ht tape H hans hhit
      have hfresh : ∃ q ∈ checkTraceQueries (codec.withOracle H) n cl.I cl.a cl.pf, q ∉ seen := by
        by_contra! hq
        have he := eight_le_seen_length (codec.withOracle H) dec n hn cl.I cl.a cl.pf
          hacc.1 seen hbefore hq
        have hlen : seen.length ≤ budget := by
          simpa only [seen,List.length_nil,zero_add] using lazyRun_seen_length_le tape default commit []
        omega
      exact hitFamily_of_fresh_generic_eligible codec dec n budget TM commit rootOf R tape
        cl (rootOf out) hF (hpref tape) rfl (hcheck tape) hacc hfresh
  have hsub : univ.filter (smallBudgetAccepts (TM := TM) codec commit rootOf claimOf R) ⊆
      (univ.filter first) ∪ (univ.filter second) := by
    intro tape htape
    rcases hcover tape (mem_filter.mp htape).2 with h | h
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,h⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,h⟩)
  have hfirst := childHit_card_le dec commit ht
  have hsecond := answerTape_hitFamily_card_le TM (extractionHits fuel budget)
    (fun p => (⟨p.1.val,lt_of_lt_of_le p.1.isLt hF⟩ : Fin TM))
    (fun p => hitTargetOf codec dec budget TM commit rootOf
      ⟨p.1.val,lt_of_lt_of_le p.1.isLt hF⟩ p.2)
    (fun p _ => hitTarget_hitTargetOf codec dec budget TM commit rootOf _ _)
  rw [extractionHits_card] at hsecond
  calc
    _ ≤ (univ.filter first).card+(univ.filter second).card :=
      (card_le_card hsub).trans (card_union_le _ _)
    _ ≤ (2*budget*budget)*Fintype.card D^(TM-1) +
        (fuel*(2*budget+1))*Fintype.card D^(TM-1) := add_le_add hfirst hsecond
    _ = _ := (Nat.add_mul _ _ _).symm

theorem smallBudget_acceptance_ratio_le (hTM : 1 ≤ TM) :
    ((univ.filter (smallBudgetAccepts (TM := TM) codec commit rootOf claimOf R)).card : ℚ)/
      (Fintype.card D : ℚ)^TM ≤
      (2*budget*budget+fuel*(2*budget+1) : ℕ)/ (Fintype.card D : ℚ) := by
  have h := smallBudget_acceptance_card_le codec dec commit rootOf claimOf R
    hbudget hn ht hF hpref hcheck
  have hd : (0 : ℚ) < Fintype.card D := by exact_mod_cast Fintype.card_pos
  have hp : (Fintype.card D : ℚ)^TM = (Fintype.card D : ℚ)^(TM-1)*Fintype.card D := by
    rw [← pow_succ, Nat.sub_add_cancel hTM]
  have hq : ((univ.filter (smallBudgetAccepts (TM := TM) codec commit rootOf claimOf R)).card : ℚ) ≤
      (2*budget*budget+fuel*(2*budget+1) : ℕ)*(Fintype.card D : ℚ)^(TM-1) := by exact_mod_cast h
  rw [hp,div_le_div_iff₀ (mul_pos (pow_pos hd _) hd) hd]
  nlinarith only [mul_le_mul_of_nonneg_right hq hd.le]

end Merkle.MH
