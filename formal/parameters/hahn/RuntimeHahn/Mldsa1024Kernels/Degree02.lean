import RuntimeHahn.HahnPolynomial
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async true
namespace RuntimeHahn.Mldsa1024
open CodingTheory.HahnDelsarte Finset
/-! Generated exact identities, split into small Gram summands. -/
private def part (degree index : ℕ) (x : ℚ) : ℚ :=
  ∑ a ∈ range (index+1),
    (Fast.choose a x * Fast.choose (index-a) (2016-x)) *
      ∑ c ∈ range (degree-index+1),
        (Fast.choose c (2016-x)*Fast.choose (degree-index-c) ((4096:ℚ)+x-2*2016))*
          hahnWeight 4096 2016 degree (a+c)
private def prefixSum (degree stop : ℕ) (x : ℚ) : ℚ :=
  ∑ i ∈ range stop, hahnWeight 4096 2016 degree i * part degree i x
private theorem prefixSum_step (degree stop : ℕ) (x : ℚ) :
    prefixSum degree (stop+1) x = prefixSum degree stop x +
      hahnWeight 4096 2016 degree stop * part degree stop x := by
  simp only [prefixSum, Finset.sum_range_succ]
private theorem prefixSum_zero (degree : ℕ) (x : ℚ) : prefixSum degree 0 x = 0 := by
  simp only [prefixSum, Finset.range_zero, Finset.sum_empty]
private theorem weight_2_0 : hahnWeight 4096 2016 2 0 = (1/1:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_2_1 : hahnWeight 4096 2016 2 1 = (-33/32:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_2_2 : hahnWeight 4096 2016 2 2 = (33/31:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem part_2_0 (x : ℚ) : part 2 0 x = (2031120/1:ℚ) + (-126946/31:ℚ)*x^1 + (2047/992:ℚ)*x^2 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_2_0, weight_2_1, weight_2_2]
  ring

private theorem part_2_1 (x : ℚ) : part 2 1 x = (-4062240/1:ℚ) + (253892/31:ℚ)*x^1 + (-2047/496:ℚ)*x^2 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_2_0, weight_2_1, weight_2_2]
  ring

private theorem part_2_2 (x : ℚ) : part 2 2 x = (2031120/1:ℚ) + (-126946/31:ℚ)*x^1 + (2047/992:ℚ)*x^2 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_2_0, weight_2_1, weight_2_2]
  ring

private theorem prefix_2_0 (x : ℚ) : prefixSum 2 1 x = (2031120/1:ℚ) + (-126946/31:ℚ)*x^1 + (2047/992:ℚ)*x^2 := by
  rw [show 1 = 0+1 from rfl, prefixSum_step, prefixSum_zero, part_2_0, weight_2_0]
  norm_num (config := { maxSteps := 10000000 })

private theorem prefix_2_1 (x : ℚ) : prefixSum 2 2 x = (6220305/1:ℚ) + (-3110177/248:ℚ)*x^1 + (100303/15872:ℚ)*x^2 := by
  rw [show 2 = 1+1 from rfl, prefixSum_step, prefix_2_0, part_2_1, weight_2_1]
  norm_num (config := { maxSteps := 10000000 })
  ring

private theorem prefix_2_2 (x : ℚ) : prefixSum 2 3 x = (8382465/1:ℚ) + (-129929231/7688:ℚ)*x^1 + (4190209/492032:ℚ)*x^2 := by
  rw [show 3 = 2+1 from rfl, prefixSum_step, prefix_2_1, part_2_2, weight_2_2]
  norm_num (config := { maxSteps := 10000000 })
  ring

theorem kernel_2 (x : ℚ) : Fast.kernel 4096 2016 2 x = (8382465/1:ℚ) + (-129929231/7688:ℚ)*x^1 + (4190209/492032:ℚ)*x^2 := by
  change prefixSum 2 3 x = _
  exact prefix_2_2 x

end RuntimeHahn.Mldsa1024
