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
private theorem weight_2_0 : hahnWeight 3584 1301 2 0 = (1/1:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_2_1 : hahnWeight 3584 1301 2 1 = (-2282/1301:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_2_2 : hahnWeight 3584 1301 2 2 = (2604903/845650:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem part_2_0 (x : ℚ) : part 2 0 x = (845650/1:ℚ) + (-6061687153/1691300:ℚ)*x^1 + (6417153/1691300:ℚ)*x^2 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_2_0, weight_2_1, weight_2_2]
  ring

private theorem part_2_1 (x : ℚ) : part 2 1 x = (-1691300/1:ℚ) + (6061687153/845650:ℚ)*x^1 + (-6417153/845650:ℚ)*x^2 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_2_0, weight_2_1, weight_2_2]
  ring

private theorem part_2_2 (x : ℚ) : part 2 2 x = (845650/1:ℚ) + (-6061687153/1691300:ℚ)*x^1 + (6417153/1691300:ℚ)*x^2 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_2_0, weight_2_1, weight_2_2]
  ring

private theorem prefix_2_0 (x : ℚ) : prefixSum 2 1 x = (845650/1:ℚ) + (-6061687153/1691300:ℚ)*x^1 + (6417153/1691300:ℚ)*x^2 := by
  rw [show 1 = 0+1 from rfl, prefixSum_step, prefixSum_zero, part_2_0, weight_2_0]
  norm_num (config := { maxSteps := 10000000 })

private theorem prefix_2_1 (x : ℚ) : prefixSum 2 2 x = (3812250/1:ℚ) + (-7110359030469/440076260:ℚ)*x^1 + (7527320469/440076260:ℚ)*x^2 := by
  rw [show 2 = 1+1 from rfl, prefixSum_step, prefix_2_0, part_2_1, weight_2_1]
  norm_num (config := { maxSteps := 10000000 })
  ring

private theorem prefix_2_2 (x : ℚ) : prefixSum 2 3 x = (6417153/1:ℚ) + (-38898773898935409/1430247845000:ℚ)*x^1 + (41179852625409/1430247845000:ℚ)*x^2 := by
  rw [show 3 = 2+1 from rfl, prefixSum_step, prefix_2_1, part_2_2, weight_2_2]
  norm_num (config := { maxSteps := 10000000 })
  ring

theorem kernel_2 (x : ℚ) : Fast.kernel 3584 1301 2 x = (6417153/1:ℚ) + (-38898773898935409/1430247845000:ℚ)*x^1 + (41179852625409/1430247845000:ℚ)*x^2 := by
  change prefixSum 2 3 x = _
  exact prefix_2_2 x

end RuntimeHahn.Kernels.Hash
