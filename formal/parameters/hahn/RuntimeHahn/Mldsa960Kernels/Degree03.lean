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
private theorem weight_3_0 : hahnWeight 3840 1888 3 0 = (1/1:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_3_1 : hahnWeight 3840 1888 3 1 = (-975/944:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_3_2 : hahnWeight 3840 1888 3 2 = (634075/593776:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_3_3 : hahnWeight 3840 1888 3 3 = (-38678575/34995673:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem part_3_0 (x : ℚ) : part 3 0 x = (-1119861536/1:ℚ) + (380180858833544/104987019:ℚ)*x^1 + (-136557962838/34995673:ℚ)*x^2 + (2353770559/1679792304:ℚ)*x^3 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_3_0, weight_3_1, weight_3_2, weight_3_3]
  ring

private theorem part_3_1 (x : ℚ) : part 3 1 x = (3359584608/1:ℚ) + (-380180858833544/34995673:ℚ)*x^1 + (409673888514/34995673:ℚ)*x^2 + (-2353770559/559930768:ℚ)*x^3 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_3_0, weight_3_1, weight_3_2, weight_3_3]
  ring

private theorem part_3_2 (x : ℚ) : part 3 2 x = (-3359584608/1:ℚ) + (380180858833544/34995673:ℚ)*x^1 + (-409673888514/34995673:ℚ)*x^2 + (2353770559/559930768:ℚ)*x^3 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_3_0, weight_3_1, weight_3_2, weight_3_3]
  ring

private theorem part_3_3 (x : ℚ) : part 3 3 x = (1119861536/1:ℚ) + (-380180858833544/104987019:ℚ)*x^1 + (136557962838/34995673:ℚ)*x^2 + (-2353770559/1679792304:ℚ)*x^3 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_3_0, weight_3_1, weight_3_2, weight_3_3]
  ring

private theorem prefix_3_0 (x : ℚ) : prefixSum 3 1 x = (-1119861536/1:ℚ) + (380180858833544/104987019:ℚ)*x^1 + (-136557962838/34995673:ℚ)*x^2 + (2353770559/1679792304:ℚ)*x^3 := by
  rw [show 1 = 0+1 from rfl, prefixSum_step, prefixSum_zero, part_3_0, weight_3_0]
  norm_num (config := { maxSteps := 10000000 })

private theorem prefix_3_1 (x : ℚ) : prefixSum 3 2 x = (-4589771486/1:ℚ) + (183864967853372717/12388468242:ℚ)*x^1 + (-264171379110111/16517957656:ℚ)*x^2 + (9106738292771/1585723934976:ℚ)*x^3 := by
  rw [show 2 = 1+1 from rfl, prefixSum_step, prefix_3_0, part_3_1, weight_3_1]
  norm_num (config := { maxSteps := 10000000 })
  ring

private theorem prefix_3_2 (x : ℚ) : prefixSum 3 3 x = (-8177367836/1:ℚ) + (103024878277050609209/3896173262109:ℚ)*x^1 + (-148022891445008547/5194897682812:ℚ)*x^2 + (5102769793873367/498710177549952:ℚ)*x^3 := by
  rw [show 3 = 2+1 from rfl, prefixSum_step, prefix_3_1, part_3_2, weight_3_2]
  norm_num (config := { maxSteps := 10000000 })
  ring

private theorem prefix_3_3 (x : ℚ) : prefixSum 3 4 x = (-9415082236/1:ℚ) + (111857314077216368603887/3674091386168787:ℚ)*x^1 + (-160713056262550243221/4898788514891716:ℚ)*x^2 + (5540235844415172481/470283697429604736:ℚ)*x^3 := by
  rw [show 4 = 3+1 from rfl, prefixSum_step, prefix_3_2, part_3_3, weight_3_3]
  norm_num (config := { maxSteps := 10000000 })
  ring

theorem kernel_3 (x : ℚ) : Fast.kernel 3840 1888 3 x = (-9415082236/1:ℚ) + (111857314077216368603887/3674091386168787:ℚ)*x^1 + (-160713056262550243221/4898788514891716:ℚ)*x^2 + (5540235844415172481/470283697429604736:ℚ)*x^3 := by
  change prefixSum 3 4 x = _
  exact prefix_3_3 x

end RuntimeHahn.Mldsa960
