import Merkle.SmallBudget

/-! Distinct positions encoded into leaf inputs give a query lower bound
equal to the number of openings. Leaf/node domain separation is not needed
for this lower bound: distinct leaf inputs alone suffice. -/

namespace Merkle.MH

open Finset RandomOracle
open scoped Classical

variable {Salt M D Enc Out Result : Type}
variable [Inhabited D] [DecidableEq Enc]
variable {n budget TM fuel : ℕ}

/-- Numbering leaves in their hash preimages ensures this property even
when leaf messages and salts are repeated. The generic codec can represent
the index in its message or salt type. -/
def OpeningClaim.DistinctLeafInputs (codec : Codec Salt M D Enc)
    (cl : OpeningClaim n Salt M D) : Prop :=
  Function.Injective (fun i : cl.I => codec.leafEnc (cl.pf.nonce i,cl.a i))

omit [Inhabited D] [DecidableEq Enc] in
theorem OpeningClaim.distinctLeafInputs_of_index
    (codec : Codec Salt M D Enc) (cl : OpeningClaim n Salt M D)
    (indexOf : Enc → Fin n)
    (hindex : ∀ i : cl.I, indexOf (codec.leafEnc (cl.pf.nonce i,cl.a i)) = i) :
    cl.DistinctLeafInputs codec := by
  intro i j he
  apply Subtype.ext
  simpa only [hindex] using congrArg indexOf he

theorem OpeningClaim.card_le_seen_length
    (codec : Codec Salt M D Enc) (cl : OpeningClaim n Salt M D)
    (hnumbered : cl.DistinctLeafInputs codec) (H : Enc → D) (seen : List Enc)
    (hqueries : ∀ q ∈ checkTraceQueries (codec.withOracle H) n cl.I cl.a cl.pf, q ∈ seen) :
    cl.I.card ≤ seen.length := by
  have hmem (i : cl.I) : codec.leafEnc (cl.pf.nonce i,cl.a i) ∈ seen := by
    apply hqueries
    apply mem_union_left
    exact mem_image.mpr ⟨i,mem_attach cl.I i,rfl⟩
  let f (i : cl.I) : seen.toFinset := ⟨_,List.mem_toFinset.mpr (hmem i)⟩
  have hinj : Function.Injective f := fun _ _ h => hnumbered (congrArg Subtype.val h)
  have hcard : cl.I.card ≤ seen.toFinset.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hinj
  exact hcard.trans (List.toFinset_card_le seen)

variable [Fintype D] [DecidableEq D]
variable (codec : Codec Salt M D Enc) (dec : RoleDecoders codec)
variable (commit : Tree Enc D Out budget) (rootOf : Out → D)
variable (claimOf : Out → OpeningClaim n Salt M D) (R : Tree Enc D Result fuel)

noncomputable def numberedBudgetAccepts (tape : Fin TM → D) : Prop :=
  let cl := claimOf (lazyRun tape default commit []).1
  smallBudgetAccepts codec commit rootOf claimOf R tape ∧
    cl.DistinctLeafInputs codec ∧ budget < cl.I.card

include dec

/-- An accepted opening of more distinct leaf inputs than the prover's
query budget requires a predictable digest hit. -/
theorem numberedBudget_acceptance_card_le
    (hF : fuel ≤ TM)
    (hpref : ∀ tape : Fin TM → D,
      (lazyRun tape default commit []).2.1 <+: runSlots TM R tape)
    (hcheck : ∀ tape : Fin TM → D,
      let cl := claimOf (lazyRun tape default commit []).1
      ∀ qa ∈ ((checkPass codec n cl.I cl.a cl.pf (2*n) fun _ => default).run
        (runOracle TM R tape)).2, qa ∈ (R.run (runOracle TM R tape)).2) :
    (univ.filter (numberedBudgetAccepts (TM := TM) codec commit rootOf claimOf R)).card ≤
      (fuel*(2*budget+1))*Fintype.card D^(TM-1) := by
  let hit := HitFamily TM (extractionHits fuel budget)
    (fun p => (⟨p.1.val,lt_of_lt_of_le p.1.isLt hF⟩ : Fin TM))
    (fun p => hitTargetOf codec dec budget TM commit rootOf
      ⟨p.1.val,lt_of_lt_of_le p.1.isLt hF⟩ p.2)
  have hsub : univ.filter (numberedBudgetAccepts (TM := TM) codec commit rootOf claimOf R) ⊆
      univ.filter hit := by
    intro tape htape
    obtain ⟨hacc,hnumbered,hbudget⟩ := (mem_filter.mp htape).2
    let out := (lazyRun tape default commit []).1
    let cl := claimOf out
    let H := runOracle TM R tape
    let seen := (lazyRun tape default commit []).2.1
    change budget < cl.I.card at hbudget
    have hfresh : ∃ q ∈ checkTraceQueries (codec.withOracle H) n cl.I cl.a cl.pf, q ∉ seen := by
      by_contra! hq
      have hc := cl.card_le_seen_length codec hnumbered H seen hq
      have hlen : seen.length ≤ budget := by
        simpa only [seen,List.length_nil,zero_add] using lazyRun_seen_length_le tape default commit []
      omega
    exact mem_filter.mpr ⟨mem_univ _,hitFamily_of_fresh_generic_eligible codec dec n budget TM
      commit rootOf R tape cl (rootOf out) hF (hpref tape) rfl (hcheck tape) hacc hfresh⟩
  have hhit := answerTape_hitFamily_card_le TM (extractionHits fuel budget)
    (fun p => (⟨p.1.val,lt_of_lt_of_le p.1.isLt hF⟩ : Fin TM))
    (fun p => hitTargetOf codec dec budget TM commit rootOf
      ⟨p.1.val,lt_of_lt_of_le p.1.isLt hF⟩ p.2)
    (fun p _ => hitTarget_hitTargetOf codec dec budget TM commit rootOf _ _)
  rw [extractionHits_card] at hhit
  exact (card_le_card hsub).trans hhit

theorem numberedBudget_acceptance_ratio_le
    (hF : fuel ≤ TM)
    (hpref : ∀ tape : Fin TM → D,
      (lazyRun tape default commit []).2.1 <+: runSlots TM R tape)
    (hcheck : ∀ tape : Fin TM → D,
      let cl := claimOf (lazyRun tape default commit []).1
      ∀ qa ∈ ((checkPass codec n cl.I cl.a cl.pf (2*n) fun _ => default).run
        (runOracle TM R tape)).2, qa ∈ (R.run (runOracle TM R tape)).2)
    (hTM : 1 ≤ TM) :
    ((univ.filter (numberedBudgetAccepts (TM := TM) codec commit rootOf claimOf R)).card : ℚ)/
      (Fintype.card D : ℚ)^TM ≤ (fuel*(2*budget+1) : ℕ)/(Fintype.card D : ℚ) := by
  have h := numberedBudget_acceptance_card_le codec dec commit rootOf claimOf R hF hpref hcheck
  have hd : (0 : ℚ) < Fintype.card D := by exact_mod_cast Fintype.card_pos
  have hp : (Fintype.card D : ℚ)^TM = (Fintype.card D : ℚ)^(TM-1)*Fintype.card D := by
    rw [← pow_succ,Nat.sub_add_cancel hTM]
  have hq : ((univ.filter (numberedBudgetAccepts (TM := TM) codec commit rootOf claimOf R)).card : ℚ) ≤
      (fuel*(2*budget+1) : ℕ)*(Fintype.card D : ℚ)^(TM-1) := by exact_mod_cast h
  rw [hp,div_le_div_iff₀ (mul_pos (pow_pos hd _) hd) hd]
  nlinarith only [mul_le_mul_of_nonneg_right hq hd.le]

end Merkle.MH
