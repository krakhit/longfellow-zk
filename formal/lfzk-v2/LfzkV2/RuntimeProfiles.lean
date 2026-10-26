import polygero.FiatShamir.StepPotential

/-! Exact step-potential certificates for the runtime V2 backend geometries.
These provide committed-list bounds and terminal budgets to the compiled
two-field theorem. RuntimeCost and RuntimeExtraction include the frontend,
MAC, and Merkle costs. RawRuntimeExtraction supplies the authenticated
raw-proof endpoint with a unit startup constant. -/

namespace LfzkV2.RuntimeProfiles

open Finset RecursivePolygero
open scoped Classical

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

structure Profile where
  n : ℕ
  k : ℕ
  s : ℕ
  t : ℕ
  cutoff : ℕ
  threshold : ℕ
  candidates : ℕ
  capacities : ℕ
  minimumField : ℕ
  queryUnits : ℕ
  positive : 1 ≤ k
  large : max (k+2*s+1) (2*k+s) ≤ n
  query_pos : 1 ≤ t
  overlap_lt : k+2*s-1 < n
  field_pos : 0 < minimumField
  cutoff_gt : k-1 < cutoff
  threshold_pos : 0 < threshold
  threshold_large : max (k+2*s+1) (2*k+s) ≤ threshold
  committedPacking : CodingTheory.UniformFamilyBound n cutoff (k-1) candidates
  systemPacking : CodingTheory.UniformFamilyBound n threshold (k+2*s-1) capacities
  rank : n.choose (k+2*s+1) ≤ minimumField^s
  query : max (((threshold-1).choose t : ℚ)/n.choose t)
    (((cutoff+s-1).choose t : ℚ)/n.choose t) ≤ queryUnits/(2^128 : ℚ)

namespace Profile

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable (p : Profile) (I : Instance F)
variable (hn : I.n = p.n) (hk : I.r+I.w = p.k) (hs : I.s = p.s) (ht : I.t = p.t)

def parameters : ProfileParameters I where
  positive_degree := by simpa only [hk] using p.positive
  large_le := by simpa only [hn,hk,hs,two_mul,Nat.add_assoc] using p.large
  query_pos := by simpa only [ht] using p.query_pos
  overlap_lt := by simpa only [hn,hk,hs] using p.overlap_lt

include hn hk in
omit [Fintype F] [DecidableEq F] in
theorem committedPacking_instance :
    CodingTheory.UniformFamilyBound I.n p.cutoff (I.r+I.w-1) p.candidates := by
  simpa only [hn,hk] using p.committedPacking

omit [Fintype F] [DecidableEq F] in
theorem systemPacking_instance :
    CodingTheory.UniformFamilyBound I.n p.threshold
      (parameters p I hn hk hs ht).overlapSize p.capacities := by
  simpa only [ProfileParameters.overlapSize,hn,hk,hs] using p.systemPacking

omit [DecidableEq F] in
theorem rank_le (hfield : p.minimumField ≤ Nat.card F) :
    (parameters p I hn hk hs ht).rankError ≤ 1/(p.minimumField : ℚ) := by
  have hqpos : (0 : ℚ) < Nat.card F := by exact_mod_cast (Nat.card_pos (α := F))
  have hminpos : (0 : ℚ) < p.minimumField := by exact_mod_cast p.field_pos
  have hq : (p.minimumField : ℚ) ≤ Nat.card F := by exact_mod_cast hfield
  have hnum : (p.n.choose (p.k+2*p.s+1) : ℚ) ≤ (Nat.card F : ℚ)^p.s := by
    exact (show (p.n.choose (p.k+2*p.s+1) : ℚ) ≤ (p.minimumField : ℚ)^p.s by
      exact_mod_cast p.rank).trans (pow_le_pow_left₀ hminpos.le hq _)
  change (I.n.choose (I.r+I.w+I.s+I.s+1) : ℚ)/(Nat.card F : ℚ)^(I.s+1) ≤ _
  rw [hn,hk,hs]
  have hexp : p.k+p.s+p.s+1 = p.k+2*p.s+1 := by omega
  rw [hexp,pow_succ,div_mul_eq_div_div]
  have hfirst : (p.n.choose (p.k+2*p.s+1) : ℚ)/(Nat.card F : ℚ)^p.s ≤ 1 :=
    (div_le_one (pow_pos hqpos _)).mpr hnum
  exact (div_le_div_of_nonneg_right hfirst hqpos.le).trans
    (one_div_le_one_div_of_le hminpos hq)

noncomputable def potential {C : Type} [Fintype C]
    (decodeCoin : C → I.layer.Coin) (decodeQuery : C → I.layer.Query)
    (kCoin kQuery : ℕ)
    (hcoin : ∀ coin, (univ.filter fun c : C => decodeCoin c = coin).card ≤ kCoin)
    (hquery : ∀ query, (univ.filter fun c : C => decodeQuery c = query).card ≤ kQuery) :
    NonrecursiveFS.TerminalPotential I p.cutoff decodeCoin decodeQuery :=
  NonrecursiveFS.stepTerminalPotential I (parameters p I hn hk hs ht)
    p.cutoff p.threshold p.capacities p.threshold_pos
    (by simpa only [ProfileParameters.largeSize,ProfileParameters.coreSize,hk,hs,two_mul,Nat.add_assoc]
      using p.threshold_large)
    (systemPacking_instance p I hn hk hs ht) decodeCoin decodeQuery kCoin kQuery hcoin hquery

private theorem normalized_mul_le {a c v : ℚ} (hc : 0 < c) (ha : a ≤ c) (hv : 0 ≤ v) :
    a*v/c ≤ v := by
  apply (div_le_iff₀ hc).mpr
  simpa only [mul_comm c v] using mul_le_mul_of_nonneg_right ha hv

/-- The two terminal rates, proved for the actual Polygero potential and
the full hash-answer alphabet. Decoder balance is the same model boundary
as for the adaptive backend theorem. -/
theorem potential_budgets_le {C : Type} [Fintype C] [Nonempty C]
    (hfield : p.minimumField ≤ Nat.card F)
    (decodeCoin : C → I.layer.Coin) (decodeQuery : C → I.layer.Query)
    (kCoin kQuery : ℕ)
    (hcoin : ∀ coin, (univ.filter fun c : C => decodeCoin c = coin).card ≤ kCoin)
    (hquery : ∀ query, (univ.filter fun c : C => decodeQuery c = query).card ≤ kQuery)
    (hkCoin : kCoin*Fintype.card I.layer.Coin ≤ Fintype.card C)
    (hkQuery : kQuery*Fintype.card I.layer.Query ≤ Fintype.card C) :
    let P := potential p I hn hk hs ht decodeCoin decodeQuery kCoin kQuery hcoin hquery
    P.challengeBudget/Fintype.card C ≤ (p.capacities+1 : ℕ)/(p.minimumField : ℚ) ∧
      P.queryBudget/Fintype.card C ≤ p.queryUnits/(2^128 : ℚ) := by
  let params := parameters p I hn hk hs ht
  have hcpos : (0 : ℚ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  have hminpos : (0 : ℚ) < p.minimumField := by exact_mod_cast p.field_pos
  have hq : (p.minimumField : ℚ) ≤ Nat.card F := by exact_mod_cast hfield
  have hchallenge : params.rankError+p.capacities/(Nat.card F : ℚ) ≤
      (p.capacities+1 : ℕ)/(p.minimumField : ℚ) := by
    have hr := rank_le p I hn hk hs ht hfield
    have hd := div_le_div_of_nonneg_left (Nat.cast_nonneg p.capacities) hminpos hq
    push_cast
    calc
      _ ≤ 1/(p.minimumField : ℚ)+p.capacities/(p.minimumField : ℚ) := add_le_add hr hd
      _ = _ := by ring
  constructor
  · refine (normalized_mul_le hcpos (by exact_mod_cast hkCoin) ?_).trans hchallenge
    unfold ProfileParameters.rankError
    positivity
  · refine (normalized_mul_le hcpos (by exact_mod_cast hkQuery) ?_).trans ?_
    · positivity
    · simpa only [hn,hs,ht] using p.query

end Profile

namespace Hash

theorem committedPacking : CodingTheory.UniformFamilyBound 3584 1404 511 22 := by
  have h := CodingTheory.InterleavedJohnson.uniformFamilyBound_of_denominator_pos
    (n := 3584) (d := 3073) (E := 2180) (by decide) (by decide) (by decide)
    (by norm_num [CodingTheory.InterleavedJohnson.denominator])
  simpa [CodingTheory.InterleavedJohnson.listBound,CodingTheory.InterleavedJohnson.denominator] using h

theorem systemPacking : CodingTheory.UniformFamilyBound 3584 1422 547 50 := by
  have h := CodingTheory.InterleavedJohnson.uniformFamilyBound_of_denominator_pos
    (n := 3584) (d := 3037) (E := 2162) (by decide) (by decide) (by decide)
    (by norm_num [CodingTheory.InterleavedJohnson.denominator])
  simpa [CodingTheory.InterleavedJohnson.listBound,CodingTheory.InterleavedJohnson.denominator] using h

def profile : Profile where
  n := 3584
  k := 512
  s := 18
  t := 87
  cutoff := 1404
  threshold := 1422
  candidates := 22
  capacities := 50
  minimumField := 2^128
  queryUnits := 737
  positive := by decide
  large := by decide
  query_pos := by decide
  overlap_lt := by decide
  field_pos := by decide
  cutoff_gt := by decide
  threshold_pos := by decide
  threshold_large := by decide
  committedPacking := committedPacking
  systemPacking := systemPacking
  rank := by norm_num [Nat.choose_eq_fast_choose,Nat.fast_choose,Nat.descFactorial,Nat.factorial]
  query := by norm_num [Nat.choose_eq_fast_choose,Nat.fast_choose,Nat.descFactorial,Nat.factorial]

end Hash

namespace Signature

-- This cutoff reduces the MAC pair count to 22*33. Its larger query tail
-- remains below the hash side's 737/2^128 rate.
theorem committedPacking : CodingTheory.UniformFamilyBound 2912 1127 415 33 := by
  have h := CodingTheory.InterleavedJohnson.uniformFamilyBound_of_denominator_pos
    (n := 2912) (d := 2497) (E := 1785) (by decide) (by decide) (by decide)
    (by norm_num [CodingTheory.InterleavedJohnson.denominator])
  simpa [CodingTheory.InterleavedJohnson.listBound,CodingTheory.InterleavedJohnson.denominator] using h

theorem systemPacking : CodingTheory.UniformFamilyBound 2912 1142 445 243 := by
  have h := CodingTheory.InterleavedJohnson.uniformFamilyBound_of_denominator_pos
    (n := 2912) (d := 2467) (E := 1770) (by decide) (by decide) (by decide)
    (by norm_num [CodingTheory.InterleavedJohnson.denominator])
  simpa [CodingTheory.InterleavedJohnson.listBound,CodingTheory.InterleavedJohnson.denominator] using h

def profile : Profile where
  n := 2912
  k := 416
  s := 15
  t := 86
  cutoff := 1127
  threshold := 1142
  candidates := 33
  capacities := 243
  minimumField := 2^255
  queryUnits := 459
  positive := by decide
  large := by decide
  query_pos := by decide
  overlap_lt := by decide
  field_pos := by decide
  cutoff_gt := by decide
  threshold_pos := by decide
  threshold_large := by decide
  committedPacking := committedPacking
  systemPacking := systemPacking
  rank := by norm_num [Nat.choose_eq_fast_choose,Nat.fast_choose,Nat.descFactorial,Nat.factorial]
  query := by norm_num [Nat.choose_eq_fast_choose,Nat.fast_choose,Nat.descFactorial,Nat.factorial]

end Signature
end LfzkV2.RuntimeProfiles
