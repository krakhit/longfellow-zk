import RuntimeHahn.KernelsMldsa960
import RuntimeHahn.Packing
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async true
namespace RuntimeHahn.Mldsa960
open CodingTheory.HahnDelsarte
/-! Generated proposal; all arithmetic and theorem bridges are checked by Lean. -/
def coefficients : List ℕ := [3780458274865464692974216771830219264, 1239435534544001854295811651210565123, 21117836584010466771415521970635648, 861962819752290845622074455532448]
def polynomial : List ℚ := [(-7964630516390932509443458739882726211369216/1:ℚ), (1528819908326146220490953941635061068153744/59:ℚ), (-391230293493921560300643293098628561035353/13924:ℚ), (141390710406199562055008605270034506167/13924:ℚ)]
private def certificatePrefix (stop : ℕ) (x : ℚ) : ℚ :=
  (coefficients.headD 0 : ℚ) +
    ∑ k ∈ Finset.Icc 1 stop, (coefficients.getD k 0 : ℚ)*Fast.kernel 3840 1888 k x
private theorem certificatePrefix_step (stop : ℕ) (x : ℚ) :
    certificatePrefix (stop+1) x = certificatePrefix stop x +
      (coefficients.getD (stop+1) 0 : ℚ)*Fast.kernel 3840 1888 (stop+1) x := by
  simp only [certificatePrefix,
    Finset.sum_Icc_succ_top (show 1 ≤ stop+1 by omega), add_assoc]
private theorem certificatePrefix_zero (x : ℚ) :
    certificatePrefix 0 x = (coefficients.headD 0 : ℚ) := by
  simp [certificatePrefix]
private theorem polynomial_prefix_1 (x : ℚ) :
    certificatePrefix 1 x = Fast.eval [(-4755651994374101655802942523876739853056/1:ℚ), (17847871697433626701859687777432137771200/3481:ℚ), (0/1:ℚ), (0/1:ℚ)] x := by
  rw [show 1 = 0+1 from rfl, certificatePrefix_step, certificatePrefix_zero, kernel_1]
  norm_num (config := { maxSteps := 10000000 }) [coefficients, Fast.eval]
  ring
private theorem polynomial_prefix_2 (x : ℚ) :
    certificatePrefix 2 x = Fast.eval [(150820315951330951478352835870196875024512/1:ℚ), (-1149296697281389806425658969681028992202992/3481:ℚ), (2514674793717959213011870030339773685959/13924:ℚ), (0/1:ℚ)] x := by
  rw [show 2 = 1+1 from rfl, certificatePrefix_step, polynomial_prefix_1, kernel_2]
  norm_num (config := { maxSteps := 10000000 }) [coefficients, Fast.eval]
  ring
private theorem polynomial_prefix_3 (x : ℚ) :
    certificatePrefix 3 x = Fast.eval [(-7964630516390932509443458739882726211369216/1:ℚ), (1528819908326146220490953941635061068153744/59:ℚ), (-391230293493921560300643293098628561035353/13924:ℚ), (141390710406199562055008605270034506167/13924:ℚ)] x := by
  rw [show 3 = 2+1 from rfl, certificatePrefix_step, polynomial_prefix_2, kernel_3]
  norm_num (config := { maxSteps := 10000000 }) [coefficients, Fast.eval]
  ring
theorem polynomial_eq (x : ℚ) : Fast.polynomial 3840 1888 coefficients x = Fast.eval polynomial x := by
  change certificatePrefix 3 x = _
  exact polynomial_prefix_3 x
theorem certificate_valid : certificateValid 3840 1888 943 coefficients = true := by
  apply Fast.certificate_of_polynomial 3840 1888 943 coefficients polynomial
    (by decide) (by decide) polynomial_eq (by decide +kernel)
  decide +kernel
theorem count_eq : certifiedBound 3840 1888 coefficients = 2417892 := by
  rw [Fast.bound_of_polynomial 3840 1888 coefficients polynomial (by decide) polynomial_eq]
  decide +kernel
theorem packing : CodingTheory.UniformFamilyBound 3840 1952 1007 2417892 := by
  apply packing_of_complement (by decide)
  simpa only [count_eq] using uniformFamilyBound_of_certificate certificate_valid
end RuntimeHahn.Mldsa960
