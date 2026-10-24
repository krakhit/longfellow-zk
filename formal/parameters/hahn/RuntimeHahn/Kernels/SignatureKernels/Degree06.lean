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
private theorem weight_6_0 : hahnWeight 2912 1050 6 0 = (1/1:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_6_1 : hahnWeight 2912 1050 6 1 = (-619/350:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_6_2 : hahnWeight 2912 1050 6 2 = (575051/183575:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_6_3 : hahnWeight 2912 1050 6 3 = (-1069019809/192386600:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_6_4 : hahnWeight 2912 1050 6 4 = (33139614079/3357146170:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_6_5 : hahnWeight 2912 1050 6 5 = (-61672821801019/3511574893820:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_6_6 : hahnWeight 2912 1050 6 6 = (39246341146103/1254133890650:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem part_6_0 (x : ℚ) : part 6 0 x = (1834797882020950/1:ℚ) + (-146584438968875356416487267/5016535562600:ℚ)*x^1 + (204041123236724660925967577/1053472468146000:ℚ)*x^2 + (-1372445665352918755137/2006614225040:ℚ)*x^3 + (40848360499543734313/30099213375600:ℚ)*x^4 + (-899602572467599/627066945325:ℚ)*x^5 + (94994784415289/150496066878000:ℚ)*x^6 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_6_0, weight_6_1, weight_6_2, weight_6_3, weight_6_4, weight_6_5, weight_6_6]
  ring

private theorem part_6_1 (x : ℚ) : part 6 1 x = (-11008787292125700/1:ℚ) + (439753316906626069249461801/2508267781300:ℚ)*x^1 + (-204041123236724660925967577/175578744691000:ℚ)*x^2 + (4117336996058756265411/1003307112520:ℚ)*x^3 + (-40848360499543734313/5016535562600:ℚ)*x^4 + (5397615434805594/627066945325:ℚ)*x^5 + (-94994784415289/25082677813000:ℚ)*x^6 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_6_0, weight_6_1, weight_6_2, weight_6_3, weight_6_4, weight_6_5, weight_6_6]
  ring

private theorem part_6_2 (x : ℚ) : part 6 2 x = (27521968230314250/1:ℚ) + (-439753316906626069249461801/1003307112520:ℚ)*x^1 + (204041123236724660925967577/70231497876400:ℚ)*x^2 + (-4117336996058756265411/401322845008:ℚ)*x^3 + (40848360499543734313/2006614225040:ℚ)*x^4 + (-2698807717402797/125413389065:ℚ)*x^5 + (94994784415289/10033071125200:ℚ)*x^6 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_6_0, weight_6_1, weight_6_2, weight_6_3, weight_6_4, weight_6_5, weight_6_6]
  ring

private theorem part_6_3 (x : ℚ) : part 6 3 x = (-36695957640419000/1:ℚ) + (146584438968875356416487267/250826778130:ℚ)*x^1 + (-204041123236724660925967577/52673623407300:ℚ)*x^2 + (1372445665352918755137/100330711252:ℚ)*x^3 + (-40848360499543734313/1504960668780:ℚ)*x^4 + (3598410289870396/125413389065:ℚ)*x^5 + (-94994784415289/7524803343900:ℚ)*x^6 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_6_0, weight_6_1, weight_6_2, weight_6_3, weight_6_4, weight_6_5, weight_6_6]
  ring

private theorem part_6_4 (x : ℚ) : part 6 4 x = (27521968230314250/1:ℚ) + (-439753316906626069249461801/1003307112520:ℚ)*x^1 + (204041123236724660925967577/70231497876400:ℚ)*x^2 + (-4117336996058756265411/401322845008:ℚ)*x^3 + (40848360499543734313/2006614225040:ℚ)*x^4 + (-2698807717402797/125413389065:ℚ)*x^5 + (94994784415289/10033071125200:ℚ)*x^6 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_6_0, weight_6_1, weight_6_2, weight_6_3, weight_6_4, weight_6_5, weight_6_6]
  ring

private theorem part_6_5 (x : ℚ) : part 6 5 x = (-11008787292125700/1:ℚ) + (439753316906626069249461801/2508267781300:ℚ)*x^1 + (-204041123236724660925967577/175578744691000:ℚ)*x^2 + (4117336996058756265411/1003307112520:ℚ)*x^3 + (-40848360499543734313/5016535562600:ℚ)*x^4 + (5397615434805594/627066945325:ℚ)*x^5 + (-94994784415289/25082677813000:ℚ)*x^6 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_6_0, weight_6_1, weight_6_2, weight_6_3, weight_6_4, weight_6_5, weight_6_6]
  ring

private theorem part_6_6 (x : ℚ) : part 6 6 x = (1834797882020950/1:ℚ) + (-146584438968875356416487267/5016535562600:ℚ)*x^1 + (204041123236724660925967577/1053472468146000:ℚ)*x^2 + (-1372445665352918755137/2006614225040:ℚ)*x^3 + (40848360499543734313/30099213375600:ℚ)*x^4 + (-899602572467599/627066945325:ℚ)*x^5 + (94994784415289/150496066878000:ℚ)*x^6 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_6_0, weight_6_1, weight_6_2, weight_6_3, weight_6_4, weight_6_5, weight_6_6]
  ring

private theorem prefix_6_0 (x : ℚ) : prefixSum 6 1 x = (1834797882020950/1:ℚ) + (-146584438968875356416487267/5016535562600:ℚ)*x^1 + (204041123236724660925967577/1053472468146000:ℚ)*x^2 + (-1372445665352918755137/2006614225040:ℚ)*x^3 + (40848360499543734313/30099213375600:ℚ)*x^4 + (-899602572467599/627066945325:ℚ)*x^5 + (94994784415289/150496066878000:ℚ)*x^6 := by
  rw [show 1 = 0+1 from rfl, prefixSum_step, prefixSum_zero, part_6_0, weight_6_0]
  norm_num (config := { maxSteps := 10000000 })

private theorem prefix_6_1 (x : ℚ) : prefixSum 6 2 x = (21304624550094688/1:ℚ) + (-37232447498094340529787765818/109736715431875:ℚ)*x^1 + (25913222651064031937597882279/11522355120346875:ℚ)*x^2 + (-24900085642831525986057/3135334726625:ℚ)*x^3 + (5187741783442054257751/329210146295625:ℚ)*x^4 + (-261141775322023024/15676673633125:ℚ)*x^5 + (12064337620741703/1646050731478125:ℚ)*x^6 := by
  rw [show 2 = 1+1 from rfl, prefixSum_step, prefix_6_0, part_6_1, weight_6_1]
  norm_num (config := { maxSteps := 10000000 })
  ring

private theorem prefix_6_2 (x : ℚ) : prefixSum 6 3 x = (107517536726646178/1:ℚ) + (-1576857622606368844465840221378911/920910515904295000:ℚ)*x^1 + (2194938308351485006892721572992141/193391208339901950000:ℚ)*x^2 + (-2109122149515415652993452803/52623458051674000:ℚ)*x^3 + (439419416397638298068467229/5525463095425770000:ℚ)*x^4 + (-1382474919955799164781/16444830641148125:ℚ)*x^5 + (1021890529218474064237/27627315477128850000:ℚ)*x^6 := by
  rw [show 3 = 2+1 from rfl, prefixSum_step, prefix_6_1, part_6_2, weight_6_2]
  norm_num (config := { maxSteps := 10000000 })
  ring

private theorem prefix_6_3 (x : ℚ) : prefixSum 6 4 x = (311423139444469613/1:ℚ) + (-1196645041867265089555850851097634697/241278555166925290000:ℚ)*x^1 + (1665693849741433365849231163647604907/50668496585054310900000:ℚ)*x^2 + (-1600569719629078276233622854981/13787346009538588000:ℚ)*x^3 + (333466419792108171306088445083/1447671331001551740000:ℚ)*x^4 + (-1049131979167863196650187/4308545627980808750:ℚ)*x^5 + (775491850113382322129099/7238356655007758700000:ℚ)*x^6 := by
  rw [show 4 = 3+1 from rfl, prefixSum_step, prefix_6_2, part_6_3, weight_6_3]
  norm_num (config := { maxSteps := 10000000 })
  ring

private theorem prefix_6_4 (x : ℚ) : prefixSum 6 5 x = (583102524154463588/1:ℚ) + (-195490124979454966644297319655720479057/21051553938314231552500:ℚ)*x^1 + (272116364895766335352883474492879464067/4420826327045988626025000:ℚ)*x^2 + (-261477350075651656962494162241261/1202945939332241803000:ℚ)*x^3 + (54476799552762944397368657947123/126309323629885389315000:ℚ)*x^4 + (-342783255772212814913991494/751841212082651126875:ℚ)*x^5 + (126688360704401628741773219/631546618149426946575000:ℚ)*x^6 := by
  rw [show 5 = 4+1 from rfl, prefixSum_step, prefix_6_3, part_6_4, weight_6_4]
  norm_num (config := { maxSteps := 10000000 })
  ring

private theorem prefix_6_5 (x : ℚ) : prefixSum 6 6 x = (776446820500658153/1:ℚ) + (-77795640172423816772827405648213365580477/6291407262707624629690000:ℚ)*x^1 + (108289187551973904365884983659262704606087/1321195525168601172234900000:ℚ)*x^2 + (-728387609824459369140759201261756447/2516562905083049851876000:ℚ)*x^3 + (21679138504808891783344810679336503/37748443576245747778140000:ℚ)*x^4 + (-477439205131018563876183709969/786425907838453078711250:ℚ)*x^5 + (50415856680380462570725752359/188742217881228738890700000:ℚ)*x^6 := by
  rw [show 6 = 5+1 from rfl, prefixSum_step, prefix_6_4, part_6_5, weight_6_5]
  norm_num (config := { maxSteps := 10000000 })
  ring

private theorem prefix_6_6 (x : ℚ) : prefixSum 6 7 x = (833864217597406842/1:ℚ) + (-41774271535453206841957499574785725875489/3145703631353812314845000:ℚ)*x^1 + (19382842513726074059991677679402517084753/220199254194766862039150000:ℚ)*x^2 + (-391125540305695166497609446930268779/1258281452541524925938000:ℚ)*x^3 + (3880381199372163923111841271111457/6291407262707624629690000:ℚ)*x^4 + (-256372657292996900163338163333/393212953919226539355625:ℚ)*x^5 + (9024009066107233877616953521/31457036313538123148450000:ℚ)*x^6 := by
  rw [show 7 = 6+1 from rfl, prefixSum_step, prefix_6_5, part_6_6, weight_6_6]
  norm_num (config := { maxSteps := 10000000 })
  ring

theorem kernel_6 (x : ℚ) : Fast.kernel 2912 1050 6 x = (833864217597406842/1:ℚ) + (-41774271535453206841957499574785725875489/3145703631353812314845000:ℚ)*x^1 + (19382842513726074059991677679402517084753/220199254194766862039150000:ℚ)*x^2 + (-391125540305695166497609446930268779/1258281452541524925938000:ℚ)*x^3 + (3880381199372163923111841271111457/6291407262707624629690000:ℚ)*x^4 + (-256372657292996900163338163333/393212953919226539355625:ℚ)*x^5 + (9024009066107233877616953521/31457036313538123148450000:ℚ)*x^6 := by
  change prefixSum 6 7 x = _
  exact prefix_6_6 x

end RuntimeHahn.Kernels.Signature
