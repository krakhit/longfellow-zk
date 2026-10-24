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
private theorem weight_4_0 : hahnWeight 3584 1301 4 0 = (1/1:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_4_1 : hahnWeight 3584 1301 4 1 = (-2280/1301:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_4_2 : hahnWeight 3584 1301 4 2 = (260034/84565:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_4_3 : hahnWeight 3584 1301 4 3 = (-197799196/36616645:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_4_4 : hahnWeight 3584 1301 4 4 = (225787782234/23764202605:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem part_4_0 (x : ℚ) : part 4 0 x = (118821013025/1:ℚ) + (-287666406394781060623/285170431260:ℚ)*x^1 + (166369732151304047/51849169320:ℚ)*x^2 + (-1292493719548997/285170431260:ℚ)*x^3 + (1368069422723/570340862520:ℚ)*x^4 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_4_0, weight_4_1, weight_4_2, weight_4_3, weight_4_4]
  ring

private theorem part_4_1 (x : ℚ) : part 4 1 x = (-475284052100/1:ℚ) + (287666406394781060623/71292607815:ℚ)*x^1 + (-166369732151304047/12962292330:ℚ)*x^2 + (1292493719548997/71292607815:ℚ)*x^3 + (-1368069422723/142585215630:ℚ)*x^4 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_4_0, weight_4_1, weight_4_2, weight_4_3, weight_4_4]
  ring

private theorem part_4_2 (x : ℚ) : part 4 2 x = (712926078150/1:ℚ) + (-287666406394781060623/47528405210:ℚ)*x^1 + (166369732151304047/8641528220:ℚ)*x^2 + (-1292493719548997/47528405210:ℚ)*x^3 + (1368069422723/95056810420:ℚ)*x^4 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_4_0, weight_4_1, weight_4_2, weight_4_3, weight_4_4]
  ring

private theorem part_4_3 (x : ℚ) : part 4 3 x = (-475284052100/1:ℚ) + (287666406394781060623/71292607815:ℚ)*x^1 + (-166369732151304047/12962292330:ℚ)*x^2 + (1292493719548997/71292607815:ℚ)*x^3 + (-1368069422723/142585215630:ℚ)*x^4 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_4_0, weight_4_1, weight_4_2, weight_4_3, weight_4_4]
  ring

private theorem part_4_4 (x : ℚ) : part 4 4 x = (118821013025/1:ℚ) + (-287666406394781060623/285170431260:ℚ)*x^1 + (166369732151304047/51849169320:ℚ)*x^2 + (-1292493719548997/285170431260:ℚ)*x^3 + (1368069422723/570340862520:ℚ)*x^4 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_4_0, weight_4_1, weight_4_2, weight_4_3, weight_4_4]
  ring

private theorem prefix_4_0 (x : ℚ) : prefixSum 4 1 x = (118821013025/1:ℚ) + (-287666406394781060623/285170431260:ℚ)*x^1 + (166369732151304047/51849169320:ℚ)*x^2 + (-1292493719548997/285170431260:ℚ)*x^3 + (1368069422723/570340862520:ℚ)*x^4 := by
  rw [show 1 = 0+1 from rfl, prefixSum_step, prefixSum_zero, part_4_0, weight_4_0]
  norm_num (config := { maxSteps := 10000000 })

private theorem prefix_4_1 (x : ℚ) : prefixSum 4 2 x = (951755401025/1:ℚ) + (-2997771621040013432752283/371006731069260:ℚ)*x^1 + (1733738978748739473787/67455769285320:ℚ)*x^2 + (-13469077051420097737/371006731069260:ℚ)*x^3 + (14256651454196383/742013462138520:ℚ)*x^4 := by
  rw [show 2 = 1+1 from rfl, prefixSum_step, prefix_4_0, part_4_1, weight_4_1]
  norm_num (config := { maxSteps := 10000000 })
  ring

private theorem prefix_4_2 (x : ℚ) : prefixSum 4 3 x = (3143974638365/1:ℚ) + (-643673433290363863037145487/24115437519501900:ℚ)*x^1 + (372263755200061245141743/4384625003545800:ℚ)*x^2 + (-2892043879557529668293/24115437519501900:ℚ)*x^3 + (3061149730132880387/48230875039003800:ℚ)*x^4 := by
  rw [show 3 = 2+1 from rfl, prefixSum_step, prefix_4_1, part_4_2, weight_4_2]
  norm_num (config := { maxSteps := 10000000 })
  ring

private theorem prefix_4_3 (x : ℚ) : prefixSum 4 4 x = (5711408202445/1:ℚ) + (-506311332219115362244110632303/10441984445944322700:ℚ)*x^1 + (292821403034679682538959567/1898542626535331400:ℚ)*x^2 + (-2274871874095774703196517/10441984445944322700:ℚ)*x^3 + (2407889960694711330403/20883968891888645400:ℚ)*x^4 := by
  rw [show 4 = 3+1 from rfl, prefixSum_step, prefix_4_2, part_4_3, weight_4_3]
  norm_num (config := { maxSteps := 10000000 })
  ring

private theorem prefix_4_4 (x : ℚ) : prefixSum 4 5 x = (6840347113615/1:ℚ) + (-393547614533308041246481276736429/6776847905417865432300:ℚ)*x^1 + (227605343422814660470943659981/1232154164621430078600:ℚ)*x^2 + (-1768221136776499385703658831/6776847905417865432300:ℚ)*x^3 + (1871613945389642468734729/13553695810835730864600:ℚ)*x^4 := by
  rw [show 5 = 4+1 from rfl, prefixSum_step, prefix_4_3, part_4_4, weight_4_4]
  norm_num (config := { maxSteps := 10000000 })
  ring

theorem kernel_4 (x : ℚ) : Fast.kernel 3584 1301 4 x = (6840347113615/1:ℚ) + (-393547614533308041246481276736429/6776847905417865432300:ℚ)*x^1 + (227605343422814660470943659981/1232154164621430078600:ℚ)*x^2 + (-1768221136776499385703658831/6776847905417865432300:ℚ)*x^3 + (1871613945389642468734729/13553695810835730864600:ℚ)*x^4 := by
  change prefixSum 4 5 x = _
  exact prefix_4_4 x

end RuntimeHahn.Kernels.Hash
