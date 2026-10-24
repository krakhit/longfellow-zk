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
private theorem weight_5_0 : hahnWeight 2912 1050 5 0 = (1/1:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_5_1 : hahnWeight 2912 1050 5 1 = (-929/525:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_5_2 : hahnWeight 2912 1050 5 2 = (1727011/550725:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_5_3 : hahnWeight 2912 1050 5 3 = (-53537341/9619330:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_5_4 : hahnWeight 2912 1050 5 4 = (99632991601/10071438510:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_5_5 : hahnWeight 2912 1050 5 5 = (-13251187882933/752480334390:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem part_5_0 (x : ℚ) : part 5 0 x = (-10534724681460/1:ℚ) + (1051005155265852005962171/7524803343900:ℚ)*x^1 + (-11135469745066958155531/15049606687800:ℚ)*x^2 + (34373810982395051371/17557874469100:ℚ)*x^3 + (-7787235824847199/3009921337560:ℚ)*x^4 + (3426620511259/2508267781300:ℚ)*x^5 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_5_0, weight_5_1, weight_5_2, weight_5_3, weight_5_4, weight_5_5]
  ring

private theorem part_5_1 (x : ℚ) : part 5 1 x = (52673623407300/1:ℚ) + (-1051005155265852005962171/1504960668780:ℚ)*x^1 + (11135469745066958155531/3009921337560:ℚ)*x^2 + (-34373810982395051371/3511574893820:ℚ)*x^3 + (7787235824847199/601984267512:ℚ)*x^4 + (-3426620511259/501653556260:ℚ)*x^5 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_5_0, weight_5_1, weight_5_2, weight_5_3, weight_5_4, weight_5_5]
  ring

private theorem part_5_2 (x : ℚ) : part 5 2 x = (-105347246814600/1:ℚ) + (1051005155265852005962171/752480334390:ℚ)*x^1 + (-11135469745066958155531/1504960668780:ℚ)*x^2 + (34373810982395051371/1755787446910:ℚ)*x^3 + (-7787235824847199/300992133756:ℚ)*x^4 + (3426620511259/250826778130:ℚ)*x^5 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_5_0, weight_5_1, weight_5_2, weight_5_3, weight_5_4, weight_5_5]
  ring

private theorem part_5_3 (x : ℚ) : part 5 3 x = (105347246814600/1:ℚ) + (-1051005155265852005962171/752480334390:ℚ)*x^1 + (11135469745066958155531/1504960668780:ℚ)*x^2 + (-34373810982395051371/1755787446910:ℚ)*x^3 + (7787235824847199/300992133756:ℚ)*x^4 + (-3426620511259/250826778130:ℚ)*x^5 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_5_0, weight_5_1, weight_5_2, weight_5_3, weight_5_4, weight_5_5]
  ring

private theorem part_5_4 (x : ℚ) : part 5 4 x = (-52673623407300/1:ℚ) + (1051005155265852005962171/1504960668780:ℚ)*x^1 + (-11135469745066958155531/3009921337560:ℚ)*x^2 + (34373810982395051371/3511574893820:ℚ)*x^3 + (-7787235824847199/601984267512:ℚ)*x^4 + (3426620511259/501653556260:ℚ)*x^5 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_5_0, weight_5_1, weight_5_2, weight_5_3, weight_5_4, weight_5_5]
  ring

private theorem part_5_5 (x : ℚ) : part 5 5 x = (10534724681460/1:ℚ) + (-1051005155265852005962171/7524803343900:ℚ)*x^1 + (11135469745066958155531/15049606687800:ℚ)*x^2 + (-34373810982395051371/17557874469100:ℚ)*x^3 + (7787235824847199/3009921337560:ℚ)*x^4 + (-3426620511259/2508267781300:ℚ)*x^5 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_5_0, weight_5_1, weight_5_2, weight_5_3, weight_5_4, weight_5_5]
  ring

private theorem prefix_5_0 (x : ℚ) : prefixSum 5 1 x = (-10534724681460/1:ℚ) + (1051005155265852005962171/7524803343900:ℚ)*x^1 + (-11135469745066958155531/15049606687800:ℚ)*x^2 + (34373810982395051371/17557874469100:ℚ)*x^3 + (-7787235824847199/3009921337560:ℚ)*x^4 + (3426620511259/2508267781300:ℚ)*x^5 := by
  rw [show 1 = 0+1 from rfl, prefixSum_step, prefixSum_zero, part_5_0, weight_5_0]
  norm_num (config := { maxSteps := 10000000 })

private theorem prefix_5_1 (x : ℚ) : prefixSum 5 2 x = (-103741955434568/1:ℚ) + (543369665272445487082442407/395052175554750:ℚ)*x^1 + (-5757037858199617366409527/790104351109500:ℚ)*x^2 + (17771260277898241558807/921788409627750:ℚ)*x^3 + (-575142988778000269/22574410031700:ℚ)*x^4 + (1771562804320903/131684058518250:ℚ)*x^5 := by
  rw [show 2 = 1+1 from rfl, prefixSum_step, prefix_5_0, part_5_1, weight_5_1]
  norm_num (config := { maxSteps := 10000000 })
  ring

private theorem prefix_5_2 (x : ℚ) : prefixSum 5 3 x = (-434098946797824/1:ℚ) + (56787910549324515586148023472/9866898384688875:ℚ)*x^1 + (-300835850632728941529825496/9866898384688875:ℚ)*x^2 + (1857285755000769415677872/23022762897607375:ℚ)*x^3 + (-210379963044071928184/1973379676937775:ℚ)*x^4 + (185147159464346288/3288966128229625:ℚ)*x^5 := by
  rw [show 3 = 2+1 from rfl, prefixSum_step, prefix_5_1, part_5_2, weight_5_2]
  norm_num (config := { maxSteps := 10000000 })
  ring

private theorem prefix_5_3 (x : ℚ) : prefixSum 5 4 x = (-1020419561240244/1:ℚ) + (163212720948683881887881619910617/12063927758346264500:ℚ)*x^1 + (-1729249668308621182696590251337/24127855516692529000:ℚ)*x^2 + (16013936349512966526515157051/84447494308423851500:ℚ)*x^3 + (-172756519423934071140339/689367300476929400:ℚ)*x^4 + (1596380534859559295979/12063927758346264500:ℚ)*x^5 := by
  rw [show 4 = 3+1 from rfl, prefixSum_step, prefix_5_2, part_5_3, weight_5_3]
  norm_num (config := { maxSteps := 10000000 })
  ring

private theorem prefix_5_4 (x : ℚ) : prefixSum 5 5 x = (-1541500107313474/1:ℚ) + (221268036005097687882908894587446407/10826513453990176227000:ℚ)*x^1 + (-2344349604890283933594738976053527/21653026907980352454000:ℚ)*x^2 + (7236715831485255781010967362807/25261864725977077863000:ℚ)*x^3 + (-1639446170401159038528877883/4330605381596070490800:ℚ)*x^4 + (721406157583761218636903/3608837817996725409000:ℚ)*x^5 := by
  rw [show 5 = 4+1 from rfl, prefixSum_step, prefix_5_3, part_5_4, weight_5_4]
  norm_num (config := { maxSteps := 10000000 })
  ring

private theorem prefix_5_5 (x : ℚ) : prefixSum 5 6 x = (-1727016737674536/1:ℚ) + (3601395822472918476734325108233583289/157285181567690615742250:ℚ)*x^1 + (-38157029030950466548093594858623529/314570363135381231484500:ℚ)*x^2 + (353358017287244279931622766658267/1100996270973834310195750:ℚ)*x^3 + (-26683902003432309612934113541/62914072627076246296900:ℚ)*x^4 + (35225184384542671637295243/157285181567690615742250:ℚ)*x^5 := by
  rw [show 6 = 5+1 from rfl, prefixSum_step, prefix_5_4, part_5_5, weight_5_5]
  norm_num (config := { maxSteps := 10000000 })
  ring

theorem kernel_5 (x : ℚ) : Fast.kernel 2912 1050 5 x = (-1727016737674536/1:ℚ) + (3601395822472918476734325108233583289/157285181567690615742250:ℚ)*x^1 + (-38157029030950466548093594858623529/314570363135381231484500:ℚ)*x^2 + (353358017287244279931622766658267/1100996270973834310195750:ℚ)*x^3 + (-26683902003432309612934113541/62914072627076246296900:ℚ)*x^4 + (35225184384542671637295243/157285181567690615742250:ℚ)*x^5 := by
  change prefixSum 5 6 x = _
  exact prefix_5_5 x

end RuntimeHahn.Kernels.Signature
