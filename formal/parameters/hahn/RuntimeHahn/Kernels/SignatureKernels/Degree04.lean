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
private theorem weight_4_0 : hahnWeight 2912 1050 4 0 = (1/1:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_4_1 : hahnWeight 2912 1050 4 1 = (-1859/1050:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_4_2 : hahnWeight 2912 1050 4 2 = (115258/36715:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_4_3 : hahnWeight 2912 1050 4 3 = (-107247569/19238660:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_4_4 : hahnWeight 2912 1050 4 4 = (14263926677/1438776930:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem part_4_0 (x : ℚ) : part 4 0 x = (50357192550/1:ℚ) + (-3070890203461107907/5755107720:ℚ)*x^1 + (853240159062091109/402857540400:ℚ)*x^2 + (-4474950687239/1198980775:ℚ)*x^3 + (992536001917/402857540400:ℚ)*x^4 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_4_0, weight_4_1, weight_4_2, weight_4_3, weight_4_4]
  ring

private theorem part_4_1 (x : ℚ) : part 4 1 x = (-201428770200/1:ℚ) + (3070890203461107907/1438776930:ℚ)*x^1 + (-853240159062091109/100714385100:ℚ)*x^2 + (17899802748956/1198980775:ℚ)*x^3 + (-992536001917/100714385100:ℚ)*x^4 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_4_0, weight_4_1, weight_4_2, weight_4_3, weight_4_4]
  ring

private theorem part_4_2 (x : ℚ) : part 4 2 x = (302143155300/1:ℚ) + (-3070890203461107907/959184620:ℚ)*x^1 + (853240159062091109/67142923400:ℚ)*x^2 + (-26849704123434/1198980775:ℚ)*x^3 + (992536001917/67142923400:ℚ)*x^4 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_4_0, weight_4_1, weight_4_2, weight_4_3, weight_4_4]
  ring

private theorem part_4_3 (x : ℚ) : part 4 3 x = (-201428770200/1:ℚ) + (3070890203461107907/1438776930:ℚ)*x^1 + (-853240159062091109/100714385100:ℚ)*x^2 + (17899802748956/1198980775:ℚ)*x^3 + (-992536001917/100714385100:ℚ)*x^4 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_4_0, weight_4_1, weight_4_2, weight_4_3, weight_4_4]
  ring

private theorem part_4_4 (x : ℚ) : part 4 4 x = (50357192550/1:ℚ) + (-3070890203461107907/5755107720:ℚ)*x^1 + (853240159062091109/402857540400:ℚ)*x^2 + (-4474950687239/1198980775:ℚ)*x^3 + (992536001917/402857540400:ℚ)*x^4 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_4_0, weight_4_1, weight_4_2, weight_4_3, weight_4_4]
  ring

private theorem prefix_4_0 (x : ℚ) : prefixSum 4 1 x = (50357192550/1:ℚ) + (-3070890203461107907/5755107720:ℚ)*x^1 + (853240159062091109/402857540400:ℚ)*x^2 + (-4474950687239/1198980775:ℚ)*x^3 + (992536001917/402857540400:ℚ)*x^4 := by
  rw [show 1 = 0+1 from rfl, prefixSum_step, prefixSum_zero, part_4_0, weight_4_0]
  norm_num (config := { maxSteps := 10000000 })

private theorem prefix_4_1 (x : ℚ) : prefixSum 4 2 x = (406982034266/1:ℚ) + (-13029787133285480849401/3021431553000:ℚ)*x^1 + (3620297994900452575487/211500208710000:ℚ)*x^2 + (-18987215765955077/629464906875:ℚ)*x^3 + (4211330256133831/211500208710000:ℚ)*x^4 := by
  rw [show 2 = 1+1 from rfl, prefixSum_step, prefix_4_0, part_4_1, weight_4_1]
  norm_num (config := { maxSteps := 10000000 })
  ring

private theorem prefix_4_2 (x : ℚ) : prefixSum 4 3 x = (1355488524626/1:ℚ) + (-45523266379163303174072189/3169481699097000:ℚ)*x^1 + (12648540479436639485386843/221863718936790000:ℚ)*x^2 + (-66337237306368215353/660308687311875:ℚ)*x^3 + (14713479744489851459/221863718936790000:ℚ)*x^4 := by
  rw [show 3 = 2+1 from rfl, prefixSum_step, prefix_4_1, part_4_2, weight_4_2]
  norm_num (config := { maxSteps := 10000000 })
  ring

private theorem prefix_4_3 (x : ℚ) : prefixSum 4 4 x = (2478370572056/1:ℚ) + (-2725932632619295212972469501/103800525645426750:ℚ)*x^1 + (757394448823734661259284187/7266036795179872500:ℚ)*x^2 + (-15889091826153167291108/86500438037855625:ℚ)*x^3 + (881042986696708596931/7266036795179872500:ℚ)*x^4 := by
  rw [show 4 = 3+1 from rfl, prefixSum_step, prefix_4_2, part_4_3, weight_4_3]
  norm_num (config := { maxSteps := 10000000 })
  ring

private theorem prefix_4_4 (x : ℚ) : prefixSum 4 5 x = (2977608005751/1:ℚ) + (-3047969084869370717617095857719/96603689200677162000:ℚ)*x^1 + (846871576150513045884452655953/6762258244047401340000:ℚ)*x^2 + (-4441549663887928571437163/20125768583474408750:ℚ)*x^3 + (985127715101383027674889/6762258244047401340000:ℚ)*x^4 := by
  rw [show 5 = 4+1 from rfl, prefixSum_step, prefix_4_3, part_4_4, weight_4_4]
  norm_num (config := { maxSteps := 10000000 })
  ring

theorem kernel_4 (x : ℚ) : Fast.kernel 2912 1050 4 x = (2977608005751/1:ℚ) + (-3047969084869370717617095857719/96603689200677162000:ℚ)*x^1 + (846871576150513045884452655953/6762258244047401340000:ℚ)*x^2 + (-4441549663887928571437163/20125768583474408750:ℚ)*x^3 + (985127715101383027674889/6762258244047401340000:ℚ)*x^4 := by
  change prefixSum 4 5 x = _
  exact prefix_4_4 x

end RuntimeHahn.Kernels.Signature
