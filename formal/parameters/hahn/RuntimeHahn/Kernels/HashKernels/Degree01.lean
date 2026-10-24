import RuntimeHahn.HahnPolynomial
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async true
namespace RuntimeHahn.Kernels.Hash
open CodingTheory.HahnDelsarte Finset
/-! Generated exact identities, split into small Gram summands. -/
private def part (degree index : ℕ) (x : ℚ) : ℚ :=
  ∑ a ∈ range (index+1),
    (Fast.choose a x * Fast.choose (index-a) (1301-x)) *
      ∑ c ∈ range (degree-index+1),
        (Fast.choose c (1301-x)*Fast.choose (degree-index-c) ((3584:ℚ)+x-2*1301))*
          hahnWeight 3584 1301 degree (a+c)
private def prefixSum (degree stop : ℕ) (x : ℚ) : ℚ :=
  ∑ i ∈ range stop, hahnWeight 3584 1301 degree i * part degree i x
private theorem prefixSum_step (degree stop : ℕ) (x : ℚ) :
    prefixSum degree (stop+1) x = prefixSum degree stop x +
      hahnWeight 3584 1301 degree stop * part degree stop x := by
  simp only [prefixSum, Finset.sum_range_succ]
private theorem prefixSum_zero (degree : ℕ) (x : ℚ) : prefixSum degree 0 x = 0 := by
  simp only [prefixSum, Finset.range_zero, Finset.sum_empty]
private theorem weight_1_0 : hahnWeight 3584 1301 1 0 = (1/1:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_1_1 : hahnWeight 3584 1301 1 1 = (-2283/1301:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem part_1_0 (x : ℚ) : part 1 0 x = (-1301/1:ℚ) + (3584/1301:ℚ)*x^1 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_1_0, weight_1_1]
  ring

private theorem part_1_1 (x : ℚ) : part 1 1 x = (1301/1:ℚ) + (-3584/1301:ℚ)*x^1 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_1_0, weight_1_1]
  ring

private theorem prefix_1_0 (x : ℚ) : prefixSum 1 1 x = (-1301/1:ℚ) + (3584/1301:ℚ)*x^1 := by
  rw [show 1 = 0+1 from rfl, prefixSum_step, prefixSum_zero, part_1_0, weight_1_0]
  norm_num (config := { maxSteps := 10000000 })

private theorem prefix_1_1 (x : ℚ) : prefixSum 1 2 x = (-3584/1:ℚ) + (12845056/1692601:ℚ)*x^1 := by
  rw [show 2 = 1+1 from rfl, prefixSum_step, prefix_1_0, part_1_1, weight_1_1]
  norm_num (config := { maxSteps := 10000000 })
  ring

theorem kernel_1 (x : ℚ) : Fast.kernel 3584 1301 1 x = (-3584/1:ℚ) + (12845056/1692601:ℚ)*x^1 := by
  change prefixSum 1 2 x = _
  exact prefix_1_1 x

end RuntimeHahn.Kernels.Hash
