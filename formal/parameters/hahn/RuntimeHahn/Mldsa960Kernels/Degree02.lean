import RuntimeHahn.HahnPolynomial
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async true
namespace RuntimeHahn.Mldsa960
open CodingTheory.HahnDelsarte Finset
/-! Generated exact identities, split into small Gram summands. -/
private def part (degree index : ℕ) (x : ℚ) : ℚ :=
  ∑ a ∈ range (index+1),
    (Fast.choose a x * Fast.choose (index-a) (1888-x)) *
      ∑ c ∈ range (degree-index+1),
        (Fast.choose c (1888-x)*Fast.choose (degree-index-c) ((3840:ℚ)+x-2*1888))*
          hahnWeight 3840 1888 degree (a+c)
private def prefixSum (degree stop : ℕ) (x : ℚ) : ℚ :=
  ∑ i ∈ range stop, hahnWeight 3840 1888 degree i * part degree i x
private theorem prefixSum_step (degree stop : ℕ) (x : ℚ) :
    prefixSum degree (stop+1) x = prefixSum degree stop x +
      hahnWeight 3840 1888 degree stop * part degree stop x := by
  simp only [prefixSum, Finset.sum_range_succ]
private theorem prefixSum_zero (degree : ℕ) (x : ℚ) : prefixSum degree 0 x = 0 := by
  simp only [prefixSum, Finset.range_zero, Finset.sum_empty]
private theorem weight_2_0 : hahnWeight 3840 1888 2 0 = (1/1:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_2_1 : hahnWeight 3840 1888 2 1 = (-1951/1888:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_2_2 : hahnWeight 3840 1888 2 2 = (119011/111333:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem part_2_0 (x : ℚ) : part 2 0 x = (1781328/1:ℚ) + (-427411226/111333:ℚ)*x^1 + (7367041/3562656:ℚ)*x^2 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_2_0, weight_2_1, weight_2_2]
  ring

private theorem part_2_1 (x : ℚ) : part 2 1 x = (-3562656/1:ℚ) + (854822452/111333:ℚ)*x^1 + (-7367041/1781328:ℚ)*x^2 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_2_0, weight_2_1, weight_2_2]
  ring

private theorem part_2_2 (x : ℚ) : part 2 2 x = (1781328/1:ℚ) + (-427411226/111333:ℚ)*x^1 + (7367041/3562656:ℚ)*x^2 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_2_0, weight_2_1, weight_2_2]
  ring

private theorem prefix_2_0 (x : ℚ) : prefixSum 2 1 x = (1781328/1:ℚ) + (-427411226/111333:ℚ)*x^1 + (7367041/3562656:ℚ)*x^2 := by
  rw [show 1 = 0+1 from rfl, prefixSum_step, prefixSum_zero, part_2_0, weight_2_0]
  norm_num (config := { maxSteps := 10000000 })

private theorem prefix_2_1 (x : ℚ) : prefixSum 2 2 x = (5462865/1:ℚ) + (-206225916545/17516392:ℚ)*x^1 + (7109194565/1121049088:ℚ)*x^2 := by
  rw [show 2 = 1+1 from rfl, prefixSum_step, prefix_2_0, part_2_1, weight_2_1]
  norm_num (config := { maxSteps := 10000000 })
  ring

private theorem prefix_2_2 (x : ℚ) : prefixSum 2 3 x = (7367041/1:ℚ) + (-1574378012901133/99160295112:ℚ)*x^1 + (54273293095681/6346258887168:ℚ)*x^2 := by
  rw [show 3 = 2+1 from rfl, prefixSum_step, prefix_2_1, part_2_2, weight_2_2]
  norm_num (config := { maxSteps := 10000000 })
  ring

theorem kernel_2 (x : ℚ) : Fast.kernel 3840 1888 2 x = (7367041/1:ℚ) + (-1574378012901133/99160295112:ℚ)*x^1 + (54273293095681/6346258887168:ℚ)*x^2 := by
  change prefixSum 2 3 x = _
  exact prefix_2_2 x

end RuntimeHahn.Mldsa960
