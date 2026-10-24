import RuntimeHahn.HahnPolynomial
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async true
namespace RuntimeHahn.Mldsa992
open CodingTheory.HahnDelsarte Finset
/-! Generated exact identities, split into small Gram summands. -/
private def part (degree index : ℕ) (x : ℚ) : ℚ :=
  ∑ a ∈ range (index+1),
    (Fast.choose a x * Fast.choose (index-a) (1952-x)) *
      ∑ c ∈ range (degree-index+1),
        (Fast.choose c (1952-x)*Fast.choose (degree-index-c) ((3968:ℚ)+x-2*1952))*
          hahnWeight 3968 1952 degree (a+c)
private def prefixSum (degree stop : ℕ) (x : ℚ) : ℚ :=
  ∑ i ∈ range stop, hahnWeight 3968 1952 degree i * part degree i x
private theorem prefixSum_step (degree stop : ℕ) (x : ℚ) :
    prefixSum degree (stop+1) x = prefixSum degree stop x +
      hahnWeight 3968 1952 degree stop * part degree stop x := by
  simp only [prefixSum, Finset.sum_range_succ]
private theorem prefixSum_zero (degree : ℕ) (x : ℚ) : prefixSum degree 0 x = 0 := by
  simp only [prefixSum, Finset.range_zero, Finset.sum_empty]
private theorem weight_3_0 : hahnWeight 3968 1952 3 0 = (1/1:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_3_1 : hahnWeight 3968 1952 3 1 = (-1007/976:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_3_2 : hahnWeight 3968 1952 3 2 = (2029105/1904176:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_3_3 : hahnWeight 3968 1952 3 3 = (-655557/595055:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem part_3_0 (x : ℚ) : part 3 0 x = (-1237714400/1:ℚ) + (6906620823092/1785165:ℚ)*x^1 + (-39313636/9755:ℚ)*x^2 + (655051/468240:ℚ)*x^3 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_3_0, weight_3_1, weight_3_2, weight_3_3]
  ring

private theorem part_3_1 (x : ℚ) : part 3 1 x = (3713143200/1:ℚ) + (-6906620823092/595055:ℚ)*x^1 + (117940908/9755:ℚ)*x^2 + (-655051/156080:ℚ)*x^3 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_3_0, weight_3_1, weight_3_2, weight_3_3]
  ring

private theorem part_3_2 (x : ℚ) : part 3 2 x = (-3713143200/1:ℚ) + (6906620823092/595055:ℚ)*x^1 + (-117940908/9755:ℚ)*x^2 + (655051/156080:ℚ)*x^3 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_3_0, weight_3_1, weight_3_2, weight_3_3]
  ring

private theorem part_3_3 (x : ℚ) : part 3 3 x = (1237714400/1:ℚ) + (-6906620823092/1785165:ℚ)*x^1 + (39313636/9755:ℚ)*x^2 + (-655051/468240:ℚ)*x^3 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_3_0, weight_3_1, weight_3_2, weight_3_3]
  ring

private theorem prefix_3_0 (x : ℚ) : prefixSum 3 1 x = (-1237714400/1:ℚ) + (6906620823092/1785165:ℚ)*x^1 + (-39313636/9755:ℚ)*x^2 + (655051/468240:ℚ)*x^3 := by
  rw [show 1 = 0+1 from rfl, prefixSum_step, prefixSum_zero, part_3_0, weight_3_0]
  norm_num (config := { maxSteps := 10000000 })

private theorem prefix_3_1 (x : ℚ) : prefixSum 3 2 x = (-5068795550/1:ℚ) + (6901440857474681/435580260:ℚ)*x^1 + (-39284150773/2380220:ℚ)*x^2 + (2618238847/457002240:ℚ)*x^3 := by
  rw [show 2 = 1+1 from rfl, prefixSum_step, prefix_3_0, part_3_1, weight_3_1]
  norm_num (config := { maxSteps := 10000000 })
  ring

private theorem prefix_3_2 (x : ℚ) : prefixSum 3 3 x = (-9025550300/1:ℚ) + (11987702623431586063/424908543630:ℚ)*x^1 + (-68235999844979/2321904610:ℚ)*x^2 + (4547842884281/445805685120:ℚ)*x^3 := by
  rw [show 3 = 2+1 from rfl, prefixSum_step, prefix_3_1, part_3_2, weight_3_2]
  norm_num (config := { maxSteps := 10000000 })
  ring

private theorem prefix_3_3 (x : ℚ) : prefixSum 3 4 x = (-10389108860/1:ℚ) + (1131047219196809423/34828569150:ℚ)*x^1 + (-6438109143859/190320050:ℚ)*x^2 + (429091812601/36541449600:ℚ)*x^3 := by
  rw [show 4 = 3+1 from rfl, prefixSum_step, prefix_3_2, part_3_3, weight_3_3]
  norm_num (config := { maxSteps := 10000000 })
  ring

theorem kernel_3 (x : ℚ) : Fast.kernel 3968 1952 3 x = (-10389108860/1:ℚ) + (1131047219196809423/34828569150:ℚ)*x^1 + (-6438109143859/190320050:ℚ)*x^2 + (429091812601/36541449600:ℚ)*x^3 := by
  change prefixSum 3 4 x = _
  exact prefix_3_3 x

end RuntimeHahn.Mldsa992
