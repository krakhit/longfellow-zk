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
private theorem weight_4_0 : hahnWeight 4096 2016 4 0 = (1/1:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_4_1 : hahnWeight 4096 2016 4 1 = (-2077/2016:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_4_2 : hahnWeight 4096 2016 4 2 = (69613/65520:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_4_3 : hahnWeight 4096 2016 4 3 = (-2297229/2094560:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_4_4 : hahnWeight 4096 2016 4 4 = (69613/61427:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem part_4_0 (x : ℚ) : part 4 0 x = (686210845320/1:ℚ) + (-1745321748091093/630435:ℚ)*x^1 + (15556149121599251/3715104960:ℚ)*x^2 + (-707855428862/251543565:ℚ)*x^3 + (6848485367/9659272896:ℚ)*x^4 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_4_0, weight_4_1, weight_4_2, weight_4_3, weight_4_4]
  ring

private theorem part_4_1 (x : ℚ) : part 4 1 x = (-2744843381280/1:ℚ) + (6981286992364372/630435:ℚ)*x^1 + (-15556149121599251/928776240:ℚ)*x^2 + (2831421715448/251543565:ℚ)*x^3 + (-6848485367/2414818224:ℚ)*x^4 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_4_0, weight_4_1, weight_4_2, weight_4_3, weight_4_4]
  ring

private theorem part_4_2 (x : ℚ) : part 4 2 x = (4117265071920/1:ℚ) + (-3490643496182186/210145:ℚ)*x^1 + (15556149121599251/619184160:ℚ)*x^2 + (-1415710857724/83847855:ℚ)*x^3 + (6848485367/1609878816:ℚ)*x^4 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_4_0, weight_4_1, weight_4_2, weight_4_3, weight_4_4]
  ring

private theorem part_4_3 (x : ℚ) : part 4 3 x = (-2744843381280/1:ℚ) + (6981286992364372/630435:ℚ)*x^1 + (-15556149121599251/928776240:ℚ)*x^2 + (2831421715448/251543565:ℚ)*x^3 + (-6848485367/2414818224:ℚ)*x^4 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_4_0, weight_4_1, weight_4_2, weight_4_3, weight_4_4]
  ring

private theorem part_4_4 (x : ℚ) : part 4 4 x = (686210845320/1:ℚ) + (-1745321748091093/630435:ℚ)*x^1 + (15556149121599251/3715104960:ℚ)*x^2 + (-707855428862/251543565:ℚ)*x^3 + (6848485367/9659272896:ℚ)*x^4 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_4_0, weight_4_1, weight_4_2, weight_4_3, weight_4_4]
  ring

private theorem prefix_4_0 (x : ℚ) : prefixSum 4 1 x = (686210845320/1:ℚ) + (-1745321748091093/630435:ℚ)*x^1 + (15556149121599251/3715104960:ℚ)*x^2 + (-707855428862/251543565:ℚ)*x^3 + (6848485367/9659272896:ℚ)*x^4 := by
  rw [show 1 = 0+1 from rfl, prefixSum_step, prefixSum_zero, part_4_0, weight_4_0]
  norm_num (config := { maxSteps := 10000000 })

private theorem prefix_4_1 (x : ℚ) : prefixSum 4 2 x = (3514107523355/1:ℚ) + (-4504675431823111033/317739240:ℚ)*x^1 + (40150420882847666831/1872412899840:ℚ)*x^2 + (-913487430946411/63388978380:ℚ)*x^3 + (17675940732227/4868273539584:ℚ)*x^4 := by
  rw [show 2 = 1+1 from rfl, prefixSum_step, prefix_4_0, part_4_1, weight_4_1]
  norm_num (config := { maxSteps := 10000000 })
  ring

private theorem prefix_4_2 (x : ℚ) : prefixSum 4 3 x = (7888575982628/1:ℚ) + (-164323787904524497043/5163262650:ℚ)*x^1 + (1464626995947691080901/30426709622400:ℚ)*x^2 + (-33322648241393081/1030070898675:ℚ)*x^3 + (644791745788417/79109445018240:ℚ)*x^4 := by
  rw [show 3 = 2+1 from rfl, prefixSum_step, prefix_4_1, part_4_2, weight_4_2]
  norm_num (config := { maxSteps := 10000000 })
  ring

private theorem prefix_4_3 (x : ℚ) : prefixSum 4 4 x = (10899009589655/1:ℚ) + (-182897730584858908682183/4159524390840:ℚ)*x^1 + (1630177572755285239544881/24511757271805440:ℚ)*x^2 + (-37089193342898373461/829825115972580:ℚ)*x^3 + (717674224215614077/63730568906694144:ℚ)*x^4 := by
  rw [show 4 = 3+1 from rfl, prefixSum_step, prefix_4_2, part_4_3, weight_4_3]
  norm_num (config := { maxSteps := 10000000 })
  ring

private theorem prefix_4_4 (x : ℚ) : prefixSum 4 5 x = (11676667550735/1:ℚ) + (-11952810452508710593536131/253730987841240:ℚ)*x^1 + (106536059626142374111660117/1495217193580131840:ℚ)*x^2 + (-2423868773256458231177/50619332074327380:ℚ)*x^3 + (46901751822013124689/3887564703308342784:ℚ)*x^4 := by
  rw [show 5 = 4+1 from rfl, prefixSum_step, prefix_4_3, part_4_4, weight_4_4]
  norm_num (config := { maxSteps := 10000000 })
  ring

theorem kernel_4 (x : ℚ) : Fast.kernel 4096 2016 4 x = (11676667550735/1:ℚ) + (-11952810452508710593536131/253730987841240:ℚ)*x^1 + (106536059626142374111660117/1495217193580131840:ℚ)*x^2 + (-2423868773256458231177/50619332074327380:ℚ)*x^3 + (46901751822013124689/3887564703308342784:ℚ)*x^4 := by
  change prefixSum 4 5 x = _
  exact prefix_4_4 x

end RuntimeHahn.Mldsa1024
