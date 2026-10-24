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
private theorem weight_3_0 : hahnWeight 3584 1301 3 0 = (1/1:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_3_1 : hahnWeight 3584 1301 3 1 = (-2281/1301:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_3_2 : hahnWeight 3584 1301 3 2 = (2602621/845650:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_3_3 : hahnWeight 3584 1301 3 3 = (-1980594581/366166450:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem part_3_0 (x : ℚ) : part 3 0 x = (-366166450/1:ℚ) + (131237078101669/56333300:ℚ)*x^1 + (-3615075567717/732332900:ℚ)*x^2 + (127558801/36616645:ℚ)*x^3 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_3_0, weight_3_1, weight_3_2, weight_3_3]
  ring

private theorem part_3_1 (x : ℚ) : part 3 1 x = (1098499350/1:ℚ) + (-393711234305007/56333300:ℚ)*x^1 + (10845226703151/732332900:ℚ)*x^2 + (-382676403/36616645:ℚ)*x^3 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_3_0, weight_3_1, weight_3_2, weight_3_3]
  ring

private theorem part_3_2 (x : ℚ) : part 3 2 x = (-1098499350/1:ℚ) + (393711234305007/56333300:ℚ)*x^1 + (-10845226703151/732332900:ℚ)*x^2 + (382676403/36616645:ℚ)*x^3 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_3_0, weight_3_1, weight_3_2, weight_3_3]
  ring

private theorem part_3_3 (x : ℚ) : part 3 3 x = (366166450/1:ℚ) + (-131237078101669/56333300:ℚ)*x^1 + (3615075567717/732332900:ℚ)*x^2 + (-127558801/36616645:ℚ)*x^3 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_3_0, weight_3_1, weight_3_2, weight_3_3]
  ring

private theorem prefix_3_0 (x : ℚ) : prefixSum 3 1 x = (-366166450/1:ℚ) + (131237078101669/56333300:ℚ)*x^1 + (-3615075567717/732332900:ℚ)*x^2 + (127558801/36616645:ℚ)*x^3 := by
  rw [show 1 = 0+1 from rfl, prefixSum_step, prefixSum_zero, part_3_0, weight_3_0]
  norm_num (config := { maxSteps := 10000000 })

private theorem prefix_3_1 (x : ℚ) : prefixSum 3 2 x = (-2292128800/1:ℚ) + (267198691014998084/18322405825:ℚ)*x^1 + (-7360293855871812/238191275725:ℚ)*x^2 + (1038838875344/47638255145:ℚ)*x^3 := by
  rw [show 2 = 1+1 from rfl, prefixSum_step, prefix_3_0, part_3_1, weight_3_1]
  norm_num (config := { maxSteps := 10000000 })
  ring

private theorem prefix_3_2 (x : ℚ) : prefixSum 3 3 x = (-5672933479/1:ℚ) + (1719397722977126641747/47638255145000:ℚ)*x^1 + (-47362778792648269971/619297316885000:ℚ)*x^2 + (1671206911625863/30964865844250:ℚ)*x^3 := by
  rw [show 3 = 2+1 from rfl, prefixSum_step, prefix_3_1, part_3_2, weight_3_2]
  norm_num (config := { maxSteps := 10000000 })
  ring

private theorem prefix_3_3 (x : ℚ) : prefixSum 3 4 x = (-7653528060/1:ℚ) + (50221332988176761216607/1031368223889250:ℚ)*x^1 + (-1383404114827124481951/13407786910560250:ℚ)*x^2 + (97627486275345606/1340778691056025:ℚ)*x^3 := by
  rw [show 4 = 3+1 from rfl, prefixSum_step, prefix_3_2, part_3_3, weight_3_3]
  norm_num (config := { maxSteps := 10000000 })
  ring

theorem kernel_3 (x : ℚ) : Fast.kernel 3584 1301 3 x = (-7653528060/1:ℚ) + (50221332988176761216607/1031368223889250:ℚ)*x^1 + (-1383404114827124481951/13407786910560250:ℚ)*x^2 + (97627486275345606/1340778691056025:ℚ)*x^3 := by
  change prefixSum 3 4 x = _
  exact prefix_3_3 x

end RuntimeHahn.Kernels.Hash
