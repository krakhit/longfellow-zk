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
private theorem weight_5_0 : hahnWeight 4096 2016 5 0 = (1/1:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_5_1 : hahnWeight 4096 2016 5 1 = (-173/168:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_5_2 : hahnWeight 4096 2016 5 2 = (11591/10920:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_5_3 : hahnWeight 4096 2016 5 3 = (-12043049/10996440:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_5_4 : hahnWeight 4096 2016 5 4 = (36129147/31942040:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem weight_5_5 : hahnWeight 4096 2016 5 5 = (-36129147/30897781:ℚ) := by
  norm_num [hahnWeight, Nat.choose_eq_fast_choose, Nat.fast_choose,
    Nat.descFactorial, Nat.factorial]
private theorem part_5_0 (x : ℚ) : part 5 0 x = (-276131244156768/1:ℚ) + (2797414532861979950832/2008355765:ℚ)*x^1 + (-355504316518862865877/126526413195:ℚ)*x^2 + (2294189711981656577/809769044448:ℚ)*x^3 + (-36136067339965/25305282639:ℚ)*x^4 + (166483617281/578406460320:ℚ)*x^5 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_5_0, weight_5_1, weight_5_2, weight_5_3, weight_5_4, weight_5_5]
  ring

private theorem part_5_1 (x : ℚ) : part 5 1 x = (1380656220783840/1:ℚ) + (-2797414532861979950832/401671153:ℚ)*x^1 + (355504316518862865877/25305282639:ℚ)*x^2 + (-11470948559908282885/809769044448:ℚ)*x^3 + (180680336699825/25305282639:ℚ)*x^4 + (-166483617281/115681292064:ℚ)*x^5 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_5_0, weight_5_1, weight_5_2, weight_5_3, weight_5_4, weight_5_5]
  ring

private theorem part_5_2 (x : ℚ) : part 5 2 x = (-2761312441567680/1:ℚ) + (5594829065723959901664/401671153:ℚ)*x^1 + (-711008633037725731754/25305282639:ℚ)*x^2 + (11470948559908282885/404884522224:ℚ)*x^3 + (-361360673399650/25305282639:ℚ)*x^4 + (166483617281/57840646032:ℚ)*x^5 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_5_0, weight_5_1, weight_5_2, weight_5_3, weight_5_4, weight_5_5]
  ring

private theorem part_5_3 (x : ℚ) : part 5 3 x = (2761312441567680/1:ℚ) + (-5594829065723959901664/401671153:ℚ)*x^1 + (711008633037725731754/25305282639:ℚ)*x^2 + (-11470948559908282885/404884522224:ℚ)*x^3 + (361360673399650/25305282639:ℚ)*x^4 + (-166483617281/57840646032:ℚ)*x^5 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_5_0, weight_5_1, weight_5_2, weight_5_3, weight_5_4, weight_5_5]
  ring

private theorem part_5_4 (x : ℚ) : part 5 4 x = (-1380656220783840/1:ℚ) + (2797414532861979950832/401671153:ℚ)*x^1 + (-355504316518862865877/25305282639:ℚ)*x^2 + (11470948559908282885/809769044448:ℚ)*x^3 + (-180680336699825/25305282639:ℚ)*x^4 + (166483617281/115681292064:ℚ)*x^5 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_5_0, weight_5_1, weight_5_2, weight_5_3, weight_5_4, weight_5_5]
  ring

private theorem part_5_5 (x : ℚ) : part 5 5 x = (276131244156768/1:ℚ) + (-2797414532861979950832/2008355765:ℚ)*x^1 + (355504316518862865877/126526413195:ℚ)*x^2 + (-2294189711981656577/809769044448:ℚ)*x^3 + (36136067339965/25305282639:ℚ)*x^4 + (-166483617281/578406460320:ℚ)*x^5 := by
  norm_num (config := { maxSteps := 10000000 }) [part, Fast.choose,
    Finset.sum_range_succ, weight_5_0, weight_5_1, weight_5_2, weight_5_3, weight_5_4, weight_5_5]
  ring

private theorem prefix_5_0 (x : ℚ) : prefixSum 5 1 x = (-276131244156768/1:ℚ) + (2797414532861979950832/2008355765:ℚ)*x^1 + (-355504316518862865877/126526413195:ℚ)*x^2 + (2294189711981656577/809769044448:ℚ)*x^3 + (-36136067339965/25305282639:ℚ)*x^4 + (166483617281/578406460320:ℚ)*x^5 := by
  rw [show 1 = 0+1 from rfl, prefixSum_step, prefixSum_zero, part_5_0, weight_5_0]
  norm_num (config := { maxSteps := 10000000 })

private theorem prefix_5_1 (x : ℚ) : prefixSum 5 2 x = (-1697878423892508/1:ℚ) + (120405383851934387050394/14058490355:ℚ)*x^1 + (-367235958963985340450941/21256437416760:ℚ)*x^2 + (2369897972477051244041/136041199467264:ℚ)*x^3 + (-37328557562183845/4251287483352:ℚ)*x^4 + (171977576651273/97172285333760:ℚ)*x^5 := by
  rw [show 2 = 1+1 from rfl, prefixSum_step, prefix_5_0, part_5_1, weight_5_1]
  norm_num (config := { maxSteps := 10000000 })
  ring

private theorem prefix_5_2 (x : ℚ) : prefixSum 5 3 x = (-4628864917501572/1:ℚ) + (4267339310942081165829598/182760374615:ℚ)*x^1 + (-13015368532072088382622847/276333686417880:ℚ)*x^2 + (83992579545360428940547/1768535593074432:ℚ)*x^3 + (-1322977561383458615/55266737283576:ℚ)*x^4 + (6095131712274691/1263239709338880:ℚ)*x^5 := by
  rw [show 3 = 2+1 from rfl, prefixSum_step, prefix_5_1, part_5_2, weight_5_2]
  norm_num (config := { maxSteps := 10000000 })
  ring

private theorem prefix_5_3 (x : ℚ) : prefixSum 5 4 x = (-7652991001771500/1:ℚ) + (202990306014269151411362450/5258277063923:ℚ)*x^1 + (-619119654825512652496442425/7950514920651576:ℚ)*x^2 + (19976943690794272351299625/254416477460850432:ℚ)*x^3 + (-314659323371162733125/7950514920651576:ℚ)*x^4 + (289935381585293525/36345211065835776:ℚ)*x^5 := by
  rw [show 4 = 3+1 from rfl, prefixSum_step, prefix_5_2, part_5_3, weight_5_3]
  norm_num (config := { maxSteps := 10000000 })
  ring

private theorem prefix_5_4 (x : ℚ) : prefixSum 5 5 x = (-9214629881353512/1:ℚ) + (74545568444065441724798309788/1603774504496515:ℚ)*x^1 + (-113681848926857466636874595191/1212453525399365340:ℚ)*x^2 + (733627458594334704375563291/7759702562555938176:ℚ)*x^3 + (-11555457296211705050095/242490705079873068:ℚ)*x^4 + (53237512314512746523/5542644687539955840:ℚ)*x^5 := by
  rw [show 5 = 4+1 from rfl, prefixSum_step, prefix_5_3, part_5_4, weight_5_4]
  norm_num (config := { maxSteps := 10000000 })
  ring

private theorem prefix_5_5 (x : ℚ) : prefixSum 5 6 x = (-9537513466793928/1:ℚ) + (38810307538775105644184157127316/806698575761747045:ℚ)*x^1 + (-59185644573069851579989302420437/609864123275880766020:ℚ)*x^2 + (381945001979561733657644507137/3903130388965636902528:ℚ)*x^3 + (-6016063205067176775935165/121972824655176153204:ℚ)*x^4 + (27716794822966481832961/2787950277832597787520:ℚ)*x^5 := by
  rw [show 6 = 5+1 from rfl, prefixSum_step, prefix_5_4, part_5_5, weight_5_5]
  norm_num (config := { maxSteps := 10000000 })
  ring

theorem kernel_5 (x : ℚ) : Fast.kernel 4096 2016 5 x = (-9537513466793928/1:ℚ) + (38810307538775105644184157127316/806698575761747045:ℚ)*x^1 + (-59185644573069851579989302420437/609864123275880766020:ℚ)*x^2 + (381945001979561733657644507137/3903130388965636902528:ℚ)*x^3 + (-6016063205067176775935165/121972824655176153204:ℚ)*x^4 + (27716794822966481832961/2787950277832597787520:ℚ)*x^5 := by
  change prefixSum 5 6 x = _
  exact prefix_5_5 x

end RuntimeHahn.Mldsa1024
