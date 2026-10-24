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
private theorem weight_3_0 : hahnWeight 4096 2016 3 0 = (1/1:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_3_1 : hahnWeight 4096 2016 3 1 = (-1039/1008:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_3_2 : hahnWeight 4096 2016 3 2 = (34287/32240:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_3_3 : hahnWeight 4096 2016 3 3 = (-34287/31217:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem part_3_0 (x : ℚ) : part 3 0 x = (-1363558560/1:ℚ) + (25108772466016/6087315:ℚ)*x^1 + (-531540612982/127833615:ℚ)*x^2 + (92162081/65978640:ℚ)*x^3 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_3_0, weight_3_1, weight_3_2, weight_3_3]
  ring

private theorem part_3_1 (x : ℚ) : part 3 1 x = (4090675680/1:ℚ) + (-25108772466016/2029105:ℚ)*x^1 + (531540612982/42611205:ℚ)*x^2 + (-92162081/21992880:ℚ)*x^3 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_3_0, weight_3_1, weight_3_2, weight_3_3]
  ring

private theorem part_3_2 (x : ℚ) : part 3 2 x = (-4090675680/1:ℚ) + (25108772466016/2029105:ℚ)*x^1 + (-531540612982/42611205:ℚ)*x^2 + (92162081/21992880:ℚ)*x^3 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_3_0, weight_3_1, weight_3_2, weight_3_3]
  ring

private theorem part_3_3 (x : ℚ) : part 3 3 x = (1363558560/1:ℚ) + (-25108772466016/6087315:ℚ)*x^1 + (531540612982/127833615:ℚ)*x^2 + (-92162081/65978640:ℚ)*x^3 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_3_0, weight_3_1, weight_3_2, weight_3_3]
  ring

private theorem prefix_3_0 (x : ℚ) : prefixSum 3 1 x = (-1363558560/1:ℚ) + (25108772466016/6087315:ℚ)*x^1 + (-531540612982/127833615:ℚ)*x^2 + (92162081/65978640:ℚ)*x^3 := by
  rw [show 1 = 0+1 from rfl, prefixSum_step, prefixSum_zero, part_3_0, weight_3_0]
  norm_num (config := { maxSteps := 10000000 })

private theorem prefix_3_1 (x : ℚ) : prefixSum 3 2 x = (-5580038750/1:ℚ) + (431557026759650/25566723:ℚ)*x^1 + (-73086834285025/4295209464:ℚ)*x^2 + (25344572275/4433764608:ℚ)*x^3 := by
  rw [show 2 = 1+1 from rfl, prefixSum_step, prefix_3_0, part_3_1, weight_3_1]
  norm_num (config := { maxSteps := 10000000 })
  ring

private theorem prefix_3_2 (x : ℚ) : prefixSum 3 3 x = (-9930441884/1:ℚ) + (7737748440676242956/257584734225:ℚ)*x^1 + (-655217622418506323/21637117674900:ℚ)*x^2 + (227212062879593/22335089212800:ℚ)*x^3 := by
  rw [show 3 = 2+1 from rfl, prefixSum_step, prefix_3_1, part_3_2, weight_3_2]
  norm_num (config := { maxSteps := 10000000 })
  ring

private theorem prefix_3_3 (x : ℚ) : prefixSum 3 4 x = (-11428098044/1:ℚ) + (289259590227942042412/8367349269825:ℚ)*x^1 + (-24493944514218367771/702857338665300:ℚ)*x^2 + (8493849174250561/725530156041600:ℚ)*x^3 := by
  rw [show 4 = 3+1 from rfl, prefixSum_step, prefix_3_2, part_3_3, weight_3_3]
  norm_num (config := { maxSteps := 10000000 })
  ring

theorem kernel_3 (x : ℚ) : Fast.kernel 4096 2016 3 x = (-11428098044/1:ℚ) + (289259590227942042412/8367349269825:ℚ)*x^1 + (-24493944514218367771/702857338665300:ℚ)*x^2 + (8493849174250561/725530156041600:ℚ)*x^3 := by
  change prefixSum 3 4 x = _
  exact prefix_3_3 x

end RuntimeHahn.Mldsa1024
