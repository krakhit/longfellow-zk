import RuntimeHahn.HahnPolynomial
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async true
namespace RuntimeHahn.Kernels.Signature
open CodingTheory.HahnDelsarte Finset
/-! Generated exact identities, split into small Gram summands. -/
private def part (degree index : ℕ) (x : ℚ) : ℚ :=
  ∑ a ∈ range (index+1),
    (Fast.choose a x * Fast.choose (index-a) (1050-x)) *
      ∑ c ∈ range (degree-index+1),
        (Fast.choose c (1050-x)*Fast.choose (degree-index-c) ((2912:ℚ)+x-2*1050))*
          hahnWeight 2912 1050 degree (a+c)
private def prefixSum (degree stop : ℕ) (x : ℚ) : ℚ :=
  ∑ i ∈ range stop, hahnWeight 2912 1050 degree i * part degree i x
private theorem prefixSum_step (degree stop : ℕ) (x : ℚ) :
    prefixSum degree (stop+1) x = prefixSum degree stop x +
      hahnWeight 2912 1050 degree stop * part degree stop x := by
  simp only [prefixSum, Finset.sum_range_succ]
private theorem prefixSum_zero (degree : ℕ) (x : ℚ) : prefixSum degree 0 x = 0 := by
  simp only [prefixSum, Finset.range_zero, Finset.sum_empty]
private theorem weight_2_0 : hahnWeight 2912 1050 2 0 = (1/1:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_2_1 : hahnWeight 2912 1050 2 1 = (-1861/1050:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_2_2 : hahnWeight 2912 1050 2 2 = (247513/78675:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem part_2_0 (x : ℚ) : part 2 0 x = (550725/1:ℚ) + (-229107344/78675:ℚ)*x^1 + (282367/73430:ℚ)*x^2 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_2_0, weight_2_1, weight_2_2]
  ring

private theorem part_2_1 (x : ℚ) : part 2 1 x = (-1101450/1:ℚ) + (458214688/78675:ℚ)*x^1 + (-282367/36715:ℚ)*x^2 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_2_0, weight_2_1, weight_2_2]
  ring

private theorem part_2_2 (x : ℚ) : part 2 2 x = (550725/1:ℚ) + (-229107344/78675:ℚ)*x^1 + (282367/73430:ℚ)*x^2 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_2_0, weight_2_1, weight_2_2]
  ring

private theorem prefix_2_0 (x : ℚ) : prefixSum 2 1 x = (550725/1:ℚ) + (-229107344/78675:ℚ)*x^1 + (282367/73430:ℚ)*x^2 := by
  rw [show 1 = 0+1 from rfl, prefixSum_step, prefixSum_zero, part_2_0, weight_2_0]
  norm_num (config := { maxSteps := 10000000 })

private theorem prefix_2_1 (x : ℚ) : prefixSum 2 2 x = (2502914/1:ℚ) + (-546650122784/41304375:ℚ)*x^1 + (336863831/19275375:ℚ)*x^2 := by
  rw [show 2 = 1+1 from rfl, prefixSum_step, prefix_2_0, part_2_1, weight_2_1]
  norm_num (config := { maxSteps := 10000000 })
  ring

private theorem prefix_2_2 (x : ℚ) : prefixSum 2 3 x = (4235505/1:ℚ) + (-64692353403248/2888552625:ℚ)*x^1 + (79731122689/2695982450:ℚ)*x^2 := by
  rw [show 3 = 2+1 from rfl, prefixSum_step, prefix_2_1, part_2_2, weight_2_2]
  norm_num (config := { maxSteps := 10000000 })
  ring

theorem kernel_2 (x : ℚ) : Fast.kernel 2912 1050 2 x = (4235505/1:ℚ) + (-64692353403248/2888552625:ℚ)*x^1 + (79731122689/2695982450:ℚ)*x^2 := by
  change prefixSum 2 3 x = _
  exact prefix_2_2 x

end RuntimeHahn.Kernels.Signature
