import RuntimeHahn.KernelsMldsa992
import RuntimeHahn.Packing
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async true
namespace RuntimeHahn.Mldsa992
open CodingTheory.HahnDelsarte
/-! Generated proposal; all arithmetic and theorem bridges are checked by Lean. -/
def coefficients : List ℕ := [8787356663501466503547399648567608832, 2191356059940867482281963398340750251, 37655280458195382366459460756947776, 1453540827137095593256950857890800]
def polynomial : List ℚ := [(-14813462838374408197971857995591242868156800/1:ℚ), (46595232736584824198239762386622314928248/1:ℚ), (-390790099526607817353155543537198486043/8:ℚ), (136546847491417123777647721289030709/8:ℚ)]
private def certificatePrefix (stop : ℕ) (x : ℚ) : ℚ :=
  (coefficients.headD 0 : ℚ) +
    ∑ k ∈ Finset.Icc 1 stop, (coefficients.getD k 0 : ℚ)*Fast.kernel 3968 1952 k x
private theorem certificatePrefix_step (stop : ℕ) (x : ℚ) :
    certificatePrefix (stop+1) x = certificatePrefix stop x +
      (coefficients.getD (stop+1) 0 : ℚ)*Fast.kernel 3968 1952 (stop+1) x := by
  simp only [certificatePrefix,
    Finset.sum_Icc_succ_top (show 1 ≤ stop+1 by omega), add_assoc]
private theorem certificatePrefix_zero (x : ℚ) :
    certificatePrefix 0 x = (coefficients.headD 0 : ℚ) := by
  simp [certificatePrefix]
private theorem polynomial_prefix_1 (x : ℚ) :
    certificatePrefix 1 x = Fast.eval [(-8686513489181860703191283364967529387136/1:ℚ), (552365422584438990287991298571924194416/61:ℚ), (0/1:ℚ), (0/1:ℚ)] x := by
  rw [show 1 = 0+1 from rfl, certificatePrefix_step, certificatePrefix_zero, kernel_1]
  norm_num (config := { maxSteps := 10000000 }) [coefficients, Fast.eval]
  ring
private theorem polynomial_prefix_2 (x : ℚ) :
    certificatePrefix 2 x = Fast.eval [(287531047207320064600886418706668324331200/1:ℚ), (-37091949579938196312364485121689148278528/61:ℚ), (2570641610806100893433802402808316709/8:ℚ), (0/1:ℚ)] x := by
  rw [show 2 = 1+1 from rfl, certificatePrefix_step, polynomial_prefix_1, kernel_2]
  norm_num (config := { maxSteps := 10000000 }) [coefficients, Fast.eval]
  ring
private theorem polynomial_prefix_3 (x : ℚ) :
    certificatePrefix 3 x = Fast.eval [(-14813462838374408197971857995591242868156800/1:ℚ), (46595232736584824198239762386622314928248/1:ℚ), (-390790099526607817353155543537198486043/8:ℚ), (136546847491417123777647721289030709/8:ℚ)] x := by
  rw [show 3 = 2+1 from rfl, certificatePrefix_step, polynomial_prefix_2, kernel_3]
  norm_num (config := { maxSteps := 10000000 }) [coefficients, Fast.eval]
  ring
theorem polynomial_eq (x : ℚ) : Fast.polynomial 3968 1952 coefficients x = Fast.eval polynomial x := by
  change certificatePrefix 3 x = _
  exact polynomial_prefix_3 x
theorem certificate_valid : certificateValid 3968 1952 975 coefficients = true := by
  apply Fast.certificate_of_polynomial 3968 1952 975 coefficients polynomial
    (by decide) (by decide) polynomial_eq (by decide +kernel)
  decide +kernel
theorem count_eq : certifiedBound 3968 1952 coefficients = 1930197 := by
  rw [Fast.bound_of_polynomial 3968 1952 coefficients polynomial (by decide) polynomial_eq]
  decide +kernel
theorem packing : CodingTheory.UniformFamilyBound 3968 2016 1039 1930197 := by
  apply packing_of_complement (by decide)
  simpa only [count_eq] using uniformFamilyBound_of_certificate certificate_valid
end RuntimeHahn.Mldsa992
