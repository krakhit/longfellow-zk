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
private theorem weight_3_0 : hahnWeight 2912 1050 3 0 = (1/1:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_3_1 : hahnWeight 2912 1050 3 1 = (-62/35:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_3_2 : hahnWeight 2912 1050 3 2 = (115382/36715:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_3_3 : hahnWeight 2912 1050 3 3 = (-7672903/1374190:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem part_3_0 (x : ℚ) : part 3 0 x = (-192386600/1:ℚ) + (6296904444893/4122570:ℚ)*x^1 + (-11097581917/2748380:ℚ)*x^2 + (205139771/57715980:ℚ)*x^3 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_3_0, weight_3_1, weight_3_2, weight_3_3]
  ring

private theorem part_3_1 (x : ℚ) : part 3 1 x = (577159800/1:ℚ) + (-6296904444893/1374190:ℚ)*x^1 + (33292745751/2748380:ℚ)*x^2 + (-205139771/19238660:ℚ)*x^3 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_3_0, weight_3_1, weight_3_2, weight_3_3]
  ring

private theorem part_3_2 (x : ℚ) : part 3 2 x = (-577159800/1:ℚ) + (6296904444893/1374190:ℚ)*x^1 + (-33292745751/2748380:ℚ)*x^2 + (205139771/19238660:ℚ)*x^3 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_3_0, weight_3_1, weight_3_2, weight_3_3]
  ring

private theorem part_3_3 (x : ℚ) : part 3 3 x = (192386600/1:ℚ) + (-6296904444893/4122570:ℚ)*x^1 + (11097581917/2748380:ℚ)*x^2 + (-205139771/57715980:ℚ)*x^3 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_3_0, weight_3_1, weight_3_2, weight_3_3]
  ring

private theorem prefix_3_0 (x : ℚ) : prefixSum 3 1 x = (-192386600/1:ℚ) + (6296904444893/4122570:ℚ)*x^1 + (-11097581917/2748380:ℚ)*x^2 + (205139771/57715980:ℚ)*x^3 := by
  rw [show 1 = 0+1 from rfl, prefixSum_step, prefixSum_zero, part_3_0, weight_3_0]
  norm_num (config := { maxSteps := 10000000 })

private theorem prefix_3_1 (x : ℚ) : prefixSum 3 2 x = (-1214783960/1:ℚ) + (1391615882321353/144289950:ℚ)*x^1 + (-2452565603657/96193300:ℚ)*x^2 + (45335889391/2020059300:ℚ)*x^3 := by
  rw [show 2 = 1+1 from rfl, prefixSum_step, prefix_3_0, part_3_1, weight_3_1]
  norm_num (config := { maxSteps := 10000000 })
  ring

private theorem prefix_3_2 (x : ℚ) : prefixSum 3 3 x = (-3028589000/1:ℚ) + (145578133861481267/6054406302:ℚ)*x^1 + (-256564996339123/4036270868:ℚ)*x^2 + (4742626365749/84761688228:ℚ)*x^3 := by
  rw [show 3 = 2+1 from rfl, prefixSum_step, prefix_3_1, part_3_2, weight_3_2]
  norm_num (config := { maxSteps := 10000000 })
  ring

private theorem prefix_3_3 (x : ℚ) : prefixSum 3 4 x = (-4102795420/1:ℚ) + (1291745535834232139503/39656361278100:ℚ)*x^1 + (-2276555413107121007/26437574185400:ℚ)*x^2 + (42082325645932441/555189057893400:ℚ)*x^3 := by
  rw [show 4 = 3+1 from rfl, prefixSum_step, prefix_3_2, part_3_3, weight_3_3]
  norm_num (config := { maxSteps := 10000000 })
  ring

theorem kernel_3 (x : ℚ) : Fast.kernel 2912 1050 3 x = (-4102795420/1:ℚ) + (1291745535834232139503/39656361278100:ℚ)*x^1 + (-2276555413107121007/26437574185400:ℚ)*x^2 + (42082325645932441/555189057893400:ℚ)*x^3 := by
  change prefixSum 3 4 x = _
  exact prefix_3_3 x

end RuntimeHahn.Kernels.Signature
