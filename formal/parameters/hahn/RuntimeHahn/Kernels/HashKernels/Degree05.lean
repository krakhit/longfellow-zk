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
private theorem weight_5_0 : hahnWeight 3584 1301 5 0 = (1/1:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_5_1 : hahnWeight 3584 1301 5 1 = (-2279/1301:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_5_2 : hahnWeight 3584 1301 5 2 = (259806/84565:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_5_3 : hahnWeight 3584 1301 5 3 = (-197539162/36616645:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_5_4 : hahnWeight 3584 1301 5 4 = (225392183842/23764202605:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_5_5 : hahnWeight 3584 1301 5 5 = (-514570355711286/30822170778685:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem part_5_0 (x : ℚ) : part 5 0 x = (-30822170778685/1:ℚ) + (605368050944622537758745487/1849330246721100:ℚ)*x^1 + (-1027793178103138313477489/739732098688440:ℚ)*x^2 + (1089675893500673961901/369866049344220:ℚ)*x^3 + (-2308581543982620151/739732098688440:ℚ)*x^4 + (203614650778259/154110853893425:ℚ)*x^5 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_5_0, weight_5_1, weight_5_2, weight_5_3, weight_5_4, weight_5_5]
  ring

private theorem part_5_1 (x : ℚ) : part 5 1 x = (154110853893425/1:ℚ) + (-605368050944622537758745487/369866049344220:ℚ)*x^1 + (1027793178103138313477489/147946419737688:ℚ)*x^2 + (-1089675893500673961901/73973209868844:ℚ)*x^3 + (2308581543982620151/147946419737688:ℚ)*x^4 + (-203614650778259/30822170778685:ℚ)*x^5 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_5_0, weight_5_1, weight_5_2, weight_5_3, weight_5_4, weight_5_5]
  ring

private theorem part_5_2 (x : ℚ) : part 5 2 x = (-308221707786850/1:ℚ) + (605368050944622537758745487/184933024672110:ℚ)*x^1 + (-1027793178103138313477489/73973209868844:ℚ)*x^2 + (1089675893500673961901/36986604934422:ℚ)*x^3 + (-2308581543982620151/73973209868844:ℚ)*x^4 + (407229301556518/30822170778685:ℚ)*x^5 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_5_0, weight_5_1, weight_5_2, weight_5_3, weight_5_4, weight_5_5]
  ring

private theorem part_5_3 (x : ℚ) : part 5 3 x = (308221707786850/1:ℚ) + (-605368050944622537758745487/184933024672110:ℚ)*x^1 + (1027793178103138313477489/73973209868844:ℚ)*x^2 + (-1089675893500673961901/36986604934422:ℚ)*x^3 + (2308581543982620151/73973209868844:ℚ)*x^4 + (-407229301556518/30822170778685:ℚ)*x^5 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_5_0, weight_5_1, weight_5_2, weight_5_3, weight_5_4, weight_5_5]
  ring

private theorem part_5_4 (x : ℚ) : part 5 4 x = (-154110853893425/1:ℚ) + (605368050944622537758745487/369866049344220:ℚ)*x^1 + (-1027793178103138313477489/147946419737688:ℚ)*x^2 + (1089675893500673961901/73973209868844:ℚ)*x^3 + (-2308581543982620151/147946419737688:ℚ)*x^4 + (203614650778259/30822170778685:ℚ)*x^5 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_5_0, weight_5_1, weight_5_2, weight_5_3, weight_5_4, weight_5_5]
  ring

private theorem part_5_5 (x : ℚ) : part 5 5 x = (30822170778685/1:ℚ) + (-605368050944622537758745487/1849330246721100:ℚ)*x^1 + (1027793178103138313477489/739732098688440:ℚ)*x^2 + (-1089675893500673961901/369866049344220:ℚ)*x^3 + (2308581543982620151/739732098688440:ℚ)*x^4 + (-203614650778259/154110853893425:ℚ)*x^5 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_5_0, weight_5_1, weight_5_2, weight_5_3, weight_5_4, weight_5_5]
  ring

private theorem prefix_5_0 (x : ℚ) : prefixSum 5 1 x = (-30822170778685/1:ℚ) + (605368050944622537758745487/1849330246721100:ℚ)*x^1 + (-1027793178103138313477489/739732098688440:ℚ)*x^2 + (1089675893500673961901/369866049344220:ℚ)*x^3 + (-2308581543982620151/739732098688440:ℚ)*x^4 + (203614650778259/154110853893425:ℚ)*x^5 := by
  rw [show 1 = 0+1 from rfl, prefixSum_step, prefixSum_zero, part_5_0, weight_5_0]
  norm_num (config := { maxSteps := 10000000 })

private theorem prefix_5_1 (x : ℚ) : prefixSum 5 2 x = (-300782690396760/1:ℚ) + (640479397899410644948752725246/200498220915345925:ℚ)*x^1 + (-543702591216560167829591681/40099644183069185:ℚ)*x^2 + (1152877095323713051691258/40099644183069185:ℚ)*x^3 + (-1221239636766806059879/40099644183069185:ℚ)*x^4 + (2585091606280776264/200498220915345925:ℚ)*x^5 := by
  rw [show 2 = 1+1 from rfl, prefixSum_step, prefix_5_0, part_5_1, weight_5_1]
  norm_num (config := { maxSteps := 10000000 })
  ring

private theorem prefix_5_2 (x : ℚ) : prefixSum 5 3 x = (-1247721128441700/1:ℚ) + (6907854829329087778365044752157/521295374379899405:ℚ)*x^1 + (-11728147955334911295091626979/208518149751959762:ℚ)*x^2 + (12434291620736190579252311/104259074875979881:ℚ)*x^3 + (-26343223998385678543061/208518149751959762:ℚ)*x^4 + (27881361360368561388/521295374379899405:ℚ)*x^5 := by
  rw [show 3 = 2+1 from rfl, prefixSum_step, prefix_5_1, part_5_2, weight_5_2]
  norm_num (config := { maxSteps := 10000000 })
  ring

private theorem prefix_5_3 (x : ℚ) : prefixSum 5 4 x = (-2910512950751560/1:ℚ) + (104658465859079447378068936501890662/3385813456597446635475:ℚ)*x^1 + (-88844511262902797434419179345357/677162691319489327095:ℚ)*x^2 + (188387555503543748246815493426/677162691319489327095:ℚ)*x^3 + (-199558435836505722866803963/677162691319489327095:ℚ)*x^4 + (140806882316517796762936/1128604485532482211825:ℚ)*x^5 := by
  rw [show 4 = 3+1 from rfl, prefixSum_step, prefix_5_2, part_5_3, weight_5_3]
  norm_num (config := { maxSteps := 10000000 })
  ring

private theorem prefix_5_4 (x : ℚ) : prefixSum 5 5 x = (-4372181262966930/1:ℚ) + (68023100733458971697547118101349996601/1464928622221161910948850:ℚ)*x^1 + (-115489541904594553977996067696271047/585971448888464764379540:ℚ)*x^2 + (122443087233883181503404286122923/292985724444232382189770:ℚ)*x^3 + (-259407272439786107175248662673/585971448888464764379540:ℚ)*x^4 + (137276817424558031003836542/732464311110580955474425:ℚ)*x^5 := by
  rw [show 5 = 4+1 from rfl, prefixSum_step, prefix_5_3, part_5_4, weight_5_4]
  norm_num (config := { maxSteps := 10000000 })
  ring

private theorem prefix_5_5 (x : ℚ) : prefixSum 5 6 x = (-4886751618678216/1:ℚ) + (246523608570809242735939476776336107934266/4750031057552117496251646125:ℚ)*x^1 + (-209273749031747462597679526322527111651/950006211510423499250329225:ℚ)*x^2 + (443747953033254149433052933130220718/950006211510423499250329225:ℚ)*x^3 + (-470061024871155171967182126097109/950006211510423499250329225:ℚ)*x^4 + (995014224277256841465289705944/4750031057552117496251646125:ℚ)*x^5 := by
  rw [show 6 = 5+1 from rfl, prefixSum_step, prefix_5_4, part_5_5, weight_5_5]
  norm_num (config := { maxSteps := 10000000 })
  ring

theorem kernel_5 (x : ℚ) : Fast.kernel 3584 1301 5 x = (-4886751618678216/1:ℚ) + (246523608570809242735939476776336107934266/4750031057552117496251646125:ℚ)*x^1 + (-209273749031747462597679526322527111651/950006211510423499250329225:ℚ)*x^2 + (443747953033254149433052933130220718/950006211510423499250329225:ℚ)*x^3 + (-470061024871155171967182126097109/950006211510423499250329225:ℚ)*x^4 + (995014224277256841465289705944/4750031057552117496251646125:ℚ)*x^5 := by
  change prefixSum 5 6 x = _
  exact prefix_5_5 x

end RuntimeHahn.Kernels.Hash
