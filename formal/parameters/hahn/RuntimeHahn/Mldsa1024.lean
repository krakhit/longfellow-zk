import RuntimeHahn.KernelsMldsa1024
import RuntimeHahn.Packing
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async true
namespace RuntimeHahn.Mldsa1024
open CodingTheory.HahnDelsarte
/-! Generated proposal; all arithmetic and theorem bridges are checked by Lean. -/
def coefficients : List ℕ := [21023791960712464318452868492487693961357639849156895744512000, 4272285990959527411518261589611627664641150129792994942271325, 89586308017367718393443199362945369572846878706446900248576, 3111541903700444961239558449009308538183808082442369904640, 21821185749821072351127825374013290121510704205921386496, 51978648860264611889463414781836780320073209102663680]
def polynomial : List ℚ := [(-275773862038725184240340032384404702332091599571809352870007296000000/1:ℚ), (4736424692651377775708514098067886009277561548454219929621844224000/3:ℚ), (-16529247549105709810665412071182590180622078139845277819682382762757536/4594941:ℚ), (18737996207508561463717101648559239565170650865478057938190375220896/4594941:ℚ), (-10570564780161466256347601896291500408634950220124660182676594944/4594941:ℚ), (2374449341732128585013605313644531508430170596451587865168384/4594941:ℚ)]
private def certificatePrefix (stop : ℕ) (x : ℚ) : ℚ :=
  (coefficients.headD 0 : ℚ) +
    ∑ k ∈ Finset.Icc 1 stop, (coefficients.getD k 0 : ℚ)*Fast.kernel 4096 2016 k x
private theorem certificatePrefix_step (stop : ℕ) (x : ℚ) :
    certificatePrefix (stop+1) x = certificatePrefix stop x +
      (coefficients.getD (stop+1) 0 : ℚ)*Fast.kernel 4096 2016 (stop+1) x := by
  simp only [certificatePrefix,
    Finset.sum_Icc_succ_top (show 1 ≤ stop+1 by omega), add_assoc]
private theorem certificatePrefix_zero (x : ℚ) :
    certificatePrefix 0 x = (coefficients.headD 0 : ℚ) := by
  simp [certificatePrefix]
private theorem polynomial_prefix_1 (x : ℚ) :
    certificatePrefix 1 x = Fast.eval [(-17478259627009511813260346602556739220408793291782950387798835200/1:ℚ), (17635962125442402900054219673518999157843437572821473704755200/1:ℚ), (0/1:ℚ), (0/1:ℚ), (0/1:ℚ), (0/1:ℚ)] x := by
  rw [show 1 = 0+1 from rfl, certificatePrefix_step, certificatePrefix_zero, kernel_1]
  norm_num (config := { maxSteps := 10000000 }) [coefficients, Fast.eval]
  ring
private theorem polynomial_prefix_2 (x : ℚ) :
    certificatePrefix 2 x = Fast.eval [(733475831807794779749633501545355118136045117824253465304380784640/1:ℚ), (-46388285612924681861246022155472450395505214044431729845923510272/31:ℚ), (23650790960883717863008520347744956785059800074197464682691872/31:ℚ), (0/1:ℚ), (0/1:ℚ), (0/1:ℚ)] x := by
  rw [show 2 = 1+1 from rfl, certificatePrefix_step, polynomial_prefix_1, kernel_2]
  norm_num (config := { maxSteps := 10000000 }) [coefficients, Fast.eval]
  ring
private theorem polynomial_prefix_3 (x : ℚ) :
    certificatePrefix 3 x = Fast.eval [(-34825530111695296643721820225001597524874831341606784784636469739520/1:ℚ), (270768969126658603453079163890333279274536239823503941460059352197265408/2552745:ℚ), (-824573657849550919464871877182878304846086489906900808882862903015008/7658235:ℚ), (278967377479582157765435454562277297120685675377201433651448421984/7658235:ℚ), (0/1:ℚ), (0/1:ℚ)] x := by
  rw [show 3 = 2+1 from rfl, certificatePrefix_step, polynomial_prefix_2, kernel_3]
  norm_num (config := { maxSteps := 10000000 }) [coefficients, Fast.eval]
  ring
private theorem polynomial_prefix_4 (x : ℚ) :
    certificatePrefix 4 x = Fast.eval [(219973201451801408711013152399884952155604533676634354355567154135040/1:ℚ), (-470668528080818255181218750825827266582831601263595883846737583728961536/510549:ℚ), (5171760946356979195266111010919778779376989313141619835805247111693216/3573843:ℚ), (-10812276148142529093379760125827265681329907787235533913964663487456/10721529:ℚ), (148556925858395369318160928177519723950903372660505696329523456/564291:ℚ), (0/1:ℚ)] x := by
  rw [show 4 = 3+1 from rfl, certificatePrefix_step, polynomial_prefix_3, kernel_4]
  norm_num (config := { maxSteps := 10000000 }) [coefficients, Fast.eval]
  ring
private theorem polynomial_prefix_5 (x : ℚ) :
    certificatePrefix 5 x = Fast.eval [(-275773862038725184240340032384404702332091599571809352870007296000000/1:ℚ), (4736424692651377775708514098067886009277561548454219929621844224000/3:ℚ), (-16529247549105709810665412071182590180622078139845277819682382762757536/4594941:ℚ), (18737996207508561463717101648559239565170650865478057938190375220896/4594941:ℚ), (-10570564780161466256347601896291500408634950220124660182676594944/4594941:ℚ), (2374449341732128585013605313644531508430170596451587865168384/4594941:ℚ)] x := by
  rw [show 5 = 4+1 from rfl, certificatePrefix_step, polynomial_prefix_4, kernel_5]
  norm_num (config := { maxSteps := 10000000 }) [coefficients, Fast.eval]
  ring
theorem polynomial_eq (x : ℚ) : Fast.polynomial 4096 2016 coefficients x = Fast.eval polynomial x := by
  change certificatePrefix 5 x = _
  exact polynomial_prefix_5 x
theorem certificate_valid : certificateValid 4096 2016 1009 coefficients = true := by
  apply Fast.certificate_of_polynomial 4096 2016 1009 coefficients polynomial
    (by decide) (by decide) polynomial_eq (by decide +kernel)
  decide +kernel
theorem count_eq : certifiedBound 4096 2016 coefficients = 43203942 := by
  rw [Fast.bound_of_polynomial 4096 2016 coefficients polynomial (by decide) polynomial_eq]
  decide +kernel
theorem packing : CodingTheory.UniformFamilyBound 4096 2080 1073 43203942 := by
  apply packing_of_complement (by decide)
  simpa only [count_eq] using uniformFamilyBound_of_certificate certificate_valid
end RuntimeHahn.Mldsa1024
