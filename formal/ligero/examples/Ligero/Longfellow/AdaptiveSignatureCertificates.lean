import examples.Ligero.Longfellow.AdaptiveCountCertificates
import examples.Ligero.Longfellow.HahnMaskFSSignature

/-! Checked v7 V1 signature local counts using the Hahn mask certificates. -/

namespace Ligero.Examples.Grid.LongfellowProfiledExtraction.Optimized

set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

/-! The signature V1 rows use the already certified Johnson line geometry
with a lower Hahn mask cutoff. The protocol is still V1: only the numerical
line and mask certificates change. -/

def v7Sig_v1_fs : Result :=
  { v7Sig_v2 with variant := .v1, certificate :=
      { v7Sig_v2.certificate with
        maskThreshold := 1626, hahnMask := HahnMask.v7SigFS } }

theorem v7Sig_v1_fs_parameters : v7Sig_v1_fs.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide,
    ?_, ?_⟩
  · change
      (decide (1626 ≤ Nat.sqrt (3187 * 909) + 1) && decide (909 < 1626) &&
        (decide (Nat.sqrt (3187 * 909) + 1 ≤ 1626) ||
          CodingTheory.HahnDelsarte.certificateValid 3187 1626 909 HahnMask.v7SigFS)) = true
    rw [HahnMask.v7SigFS_valid]
    native_decide
  · change v7Sig_v1_fs.certificate.inverseJohnsonConditions
      (v7Sig_v1_fs.etaDenominators
        (v7Sig_v1_fs.certificate.n - v7Sig_v1_fs.certificate.e))
      v7Sig_v1_fs.etaDenominators = true
    native_decide

def v7Sig_v1_fs_counts : CountCertificate v7Sig_v1_fs :=
  ⟨1625, 1625, 132, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

end Ligero.Examples.Grid.LongfellowProfiledExtraction.Optimized
