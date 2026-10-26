import examples.Ligero.Longfellow.ProfiledExtraction
import examples.Ligero.Longfellow.HahnMaskCertificates

/-! Best-found scalar IOP certificates with per-agreement Johnson parameters.
All arithmetic and geometry checks are connected to actual RS verifiers. V2/V3
share parameter data and checks; their concrete verifier bridges stay distinct.
V1 records certify the unchecked-mask list below the Johnson threshold with
Hahn/Delsarte certificates (`HahnMaskCertificates`), checked in `_parameters`. -/
namespace Ligero.Examples.Grid.LongfellowProfiledExtraction.Optimized
open Ligero.Examples.Grid.LongfellowProfiledExtraction
set_option maxHeartbeats 20000000
set_option maxRecDepth 10000

def v7Sig_v2 : Result :=
  { variant := .v2, route := .johnson, etaBits := 0, adaptiveEta := true
    certificate :=
      { n := 3187, k := 455, d := 2733, e := 1980, g := 0, m := 7199076871903652
        fieldBits := 256, fieldOrder := 115792089210356248762697446949407573530086143415290314195533631308867097853951
        openings := 132, targetBits := 191 } }

theorem v7Sig_v2_parameters : v7Sig_v2.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, by trivial, ?_⟩
  change v7Sig_v2.certificate.inverseJohnsonConditions
    (v7Sig_v2.etaDenominators (v7Sig_v2.certificate.n - v7Sig_v2.certificate.e))
    v7Sig_v2.etaDenominators = true
  native_decide

theorem v7Sig_v2_compressed_bound :
    v7Sig_v2.compressedBound ≤ (1 : ℚ) / 2 ^ v7Sig_v2.certificate.targetBits := by native_decide

theorem v7Sig_v2_bound :
    v7Sig_v2.bound ≤ (1 : ℚ) / 2 ^ v7Sig_v2.certificate.targetBits := by
  rw [← Result.compressedBound_eq]; exact v7Sig_v2_compressed_bound

def v7Sig_v2_certified : CertifiedResult :=
  ⟨v7Sig_v2, v7Sig_v2_parameters, v7Sig_v2_bound⟩

def v7Sig_v2_extraction := @CertifiedResult.v2_extraction v7Sig_v2_certified rfl

def v7Sig_v2_interactive := @CertifiedResult.v2_interactive v7Sig_v2_certified rfl

def v7Sig_v2_uniform_envelope := @CertifiedResult.v2_uniform_envelope v7Sig_v2_certified rfl

def v7Sig_v3 : Result := { v7Sig_v2 with variant := .v3 }

theorem v7Sig_v3_parameters : v7Sig_v3.ParametersValid := v7Sig_v2_parameters

theorem v7Sig_v3_compressed_bound :
    v7Sig_v3.compressedBound ≤ (1 : ℚ) / 2 ^ v7Sig_v3.certificate.targetBits := v7Sig_v2_compressed_bound

theorem v7Sig_v3_bound :
    v7Sig_v3.bound ≤ (1 : ℚ) / 2 ^ v7Sig_v3.certificate.targetBits := by
  rw [← Result.compressedBound_eq]; exact v7Sig_v3_compressed_bound

def v7Sig_v3_certified : CertifiedResult :=
  ⟨v7Sig_v3, v7Sig_v3_parameters, v7Sig_v3_bound⟩

def v7Sig_v3_extraction := @CertifiedResult.v3_extraction v7Sig_v3_certified rfl

def v7Sig_v3_interactive := @CertifiedResult.v3_interactive v7Sig_v3_certified rfl

def v7Sig_v3_uniform_envelope := @CertifiedResult.v3_uniform_envelope v7Sig_v3_certified rfl

def v7Sig_v1 : Result :=
  { variant := .v1, route := .triples, etaBits := 0, adaptiveEta := false
    certificate :=
      { n := 3187, k := 455, d := 2733, e := 1522, g := 0, m := 8726582
        fieldBits := 256, fieldOrder := 115792089210356248762697446949407573530086143415290314195533631308867097853951
        openings := 132, targetBits := 127
        maskThreshold := 1665, hahnMask := HahnMask.v7Sig } }

theorem v7Sig_v1_parameters : v7Sig_v1.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, by change (decide (1665 ≤ Nat.sqrt (3187 * 909) + 1) && decide (909 < 1665) && (decide (Nat.sqrt (3187 * 909) + 1 ≤ 1665) || CodingTheory.HahnDelsarte.certificateValid 3187 1665 909 HahnMask.v7Sig)) = true; rw [HahnMask.v7Sig_valid]; decide +kernel, ?_⟩
  exact v7Sig_v1.certificate.conditions_of_checked
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

theorem v7Sig_v1_compressed_bound :
    v7Sig_v1.compressedBound ≤ (1 : ℚ) / 2 ^ v7Sig_v1.certificate.targetBits := by native_decide

theorem v7Sig_v1_bound :
    v7Sig_v1.bound ≤ (1 : ℚ) / 2 ^ v7Sig_v1.certificate.targetBits := by
  rw [← Result.compressedBound_eq]; exact v7Sig_v1_compressed_bound

def v7Sig_v1_certified : CertifiedResult :=
  ⟨v7Sig_v1, v7Sig_v1_parameters, v7Sig_v1_bound⟩

def v7Sig_v1_extraction := @CertifiedResult.v1_extraction v7Sig_v1_certified rfl

def v7Sig_v1_interactive := @CertifiedResult.v1_interactive v7Sig_v1_certified rfl

def v7Sig_v1_uniform_envelope := @CertifiedResult.v1_uniform_envelope v7Sig_v1_certified rfl

def v7Hash1_v2 : Result :=
  { variant := .v2, route := .johnson, etaBits := 0, adaptiveEta := true
    certificate :=
      { n := 3230, k := 461, d := 2770, e := 1670, g := 23, m := 9433738746
        fieldBits := 128, fieldOrder := 0
        openings := 132, targetBits := 126 } }

theorem v7Hash1_v2_parameters : v7Hash1_v2.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, by trivial, ?_⟩
  change v7Hash1_v2.certificate.inverseJohnsonConditions
    (v7Hash1_v2.etaDenominators (v7Hash1_v2.certificate.n - v7Hash1_v2.certificate.e))
    v7Hash1_v2.etaDenominators = true
  native_decide

theorem v7Hash1_v2_compressed_bound :
    v7Hash1_v2.compressedBound ≤ (1 : ℚ) / 2 ^ v7Hash1_v2.certificate.targetBits := by native_decide

theorem v7Hash1_v2_bound :
    v7Hash1_v2.bound ≤ (1 : ℚ) / 2 ^ v7Hash1_v2.certificate.targetBits := by
  rw [← Result.compressedBound_eq]; exact v7Hash1_v2_compressed_bound

def v7Hash1_v2_certified : CertifiedResult :=
  ⟨v7Hash1_v2, v7Hash1_v2_parameters, v7Hash1_v2_bound⟩

def v7Hash1_v2_extraction := @CertifiedResult.v2_extraction v7Hash1_v2_certified rfl

def v7Hash1_v2_interactive := @CertifiedResult.v2_interactive v7Hash1_v2_certified rfl

def v7Hash1_v2_uniform_envelope := @CertifiedResult.v2_uniform_envelope v7Hash1_v2_certified rfl

def v7Hash1_v3 : Result := { v7Hash1_v2 with variant := .v3 }

theorem v7Hash1_v3_parameters : v7Hash1_v3.ParametersValid := v7Hash1_v2_parameters

theorem v7Hash1_v3_compressed_bound :
    v7Hash1_v3.compressedBound ≤ (1 : ℚ) / 2 ^ v7Hash1_v3.certificate.targetBits := v7Hash1_v2_compressed_bound

theorem v7Hash1_v3_bound :
    v7Hash1_v3.bound ≤ (1 : ℚ) / 2 ^ v7Hash1_v3.certificate.targetBits := by
  rw [← Result.compressedBound_eq]; exact v7Hash1_v3_compressed_bound

def v7Hash1_v3_certified : CertifiedResult :=
  ⟨v7Hash1_v3, v7Hash1_v3_parameters, v7Hash1_v3_bound⟩

def v7Hash1_v3_extraction := @CertifiedResult.v3_extraction v7Hash1_v3_certified rfl

def v7Hash1_v3_interactive := @CertifiedResult.v3_interactive v7Hash1_v3_certified rfl

def v7Hash1_v3_uniform_envelope := @CertifiedResult.v3_uniform_envelope v7Hash1_v3_certified rfl

def v7Hash1_v1 : Result :=
  { variant := .v1, route := .triples, etaBits := 0, adaptiveEta := false
    certificate :=
      { n := 3230, k := 461, d := 2770, e := 1543, g := 16, m := 1200474
        fieldBits := 128, fieldOrder := 0
        openings := 132, targetBits := 125
        maskThreshold := 1681, hahnMask := HahnMask.v7Hash1 } }

theorem v7Hash1_v1_parameters : v7Hash1_v1.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, by change (decide (1681 ≤ Nat.sqrt (3230 * 921) + 1) && decide (921 < 1681) && (decide (Nat.sqrt (3230 * 921) + 1 ≤ 1681) || CodingTheory.HahnDelsarte.certificateValid 3230 1681 921 HahnMask.v7Hash1)) = true; rw [HahnMask.v7Hash1_valid]; decide +kernel, ?_⟩
  exact v7Hash1_v1.certificate.conditions_of_checked
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

theorem v7Hash1_v1_compressed_bound :
    v7Hash1_v1.compressedBound ≤ (1 : ℚ) / 2 ^ v7Hash1_v1.certificate.targetBits := by native_decide

theorem v7Hash1_v1_bound :
    v7Hash1_v1.bound ≤ (1 : ℚ) / 2 ^ v7Hash1_v1.certificate.targetBits := by
  rw [← Result.compressedBound_eq]; exact v7Hash1_v1_compressed_bound

def v7Hash1_v1_certified : CertifiedResult :=
  ⟨v7Hash1_v1, v7Hash1_v1_parameters, v7Hash1_v1_bound⟩

def v7Hash1_v1_extraction := @CertifiedResult.v1_extraction v7Hash1_v1_certified rfl

def v7Hash1_v1_interactive := @CertifiedResult.v1_interactive v7Hash1_v1_certified rfl

def v7Hash1_v1_uniform_envelope := @CertifiedResult.v1_uniform_envelope v7Hash1_v1_certified rfl

def v7Hash2_v2 : Result :=
  { variant := .v2, route := .johnson, etaBits := 0, adaptiveEta := true
    certificate :=
      { n := 3318, k := 474, d := 2845, e := 1715, g := 23, m := 9678434277
        fieldBits := 128, fieldOrder := 0
        openings := 132, targetBits := 126 } }

theorem v7Hash2_v2_parameters : v7Hash2_v2.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, by trivial, ?_⟩
  change v7Hash2_v2.certificate.inverseJohnsonConditions
    (v7Hash2_v2.etaDenominators (v7Hash2_v2.certificate.n - v7Hash2_v2.certificate.e))
    v7Hash2_v2.etaDenominators = true
  native_decide

theorem v7Hash2_v2_compressed_bound :
    v7Hash2_v2.compressedBound ≤ (1 : ℚ) / 2 ^ v7Hash2_v2.certificate.targetBits := by native_decide

theorem v7Hash2_v2_bound :
    v7Hash2_v2.bound ≤ (1 : ℚ) / 2 ^ v7Hash2_v2.certificate.targetBits := by
  rw [← Result.compressedBound_eq]; exact v7Hash2_v2_compressed_bound

def v7Hash2_v2_certified : CertifiedResult :=
  ⟨v7Hash2_v2, v7Hash2_v2_parameters, v7Hash2_v2_bound⟩

def v7Hash2_v2_extraction := @CertifiedResult.v2_extraction v7Hash2_v2_certified rfl

def v7Hash2_v2_interactive := @CertifiedResult.v2_interactive v7Hash2_v2_certified rfl

def v7Hash2_v2_uniform_envelope := @CertifiedResult.v2_uniform_envelope v7Hash2_v2_certified rfl

def v7Hash2_v3 : Result := { v7Hash2_v2 with variant := .v3 }

theorem v7Hash2_v3_parameters : v7Hash2_v3.ParametersValid := v7Hash2_v2_parameters

theorem v7Hash2_v3_compressed_bound :
    v7Hash2_v3.compressedBound ≤ (1 : ℚ) / 2 ^ v7Hash2_v3.certificate.targetBits := v7Hash2_v2_compressed_bound

theorem v7Hash2_v3_bound :
    v7Hash2_v3.bound ≤ (1 : ℚ) / 2 ^ v7Hash2_v3.certificate.targetBits := by
  rw [← Result.compressedBound_eq]; exact v7Hash2_v3_compressed_bound

def v7Hash2_v3_certified : CertifiedResult :=
  ⟨v7Hash2_v3, v7Hash2_v3_parameters, v7Hash2_v3_bound⟩

def v7Hash2_v3_extraction := @CertifiedResult.v3_extraction v7Hash2_v3_certified rfl

def v7Hash2_v3_interactive := @CertifiedResult.v3_interactive v7Hash2_v3_certified rfl

def v7Hash2_v3_uniform_envelope := @CertifiedResult.v3_uniform_envelope v7Hash2_v3_certified rfl

def v7Hash2_v1 : Result :=
  { variant := .v1, route := .triples, etaBits := 0, adaptiveEta := false
    certificate :=
      { n := 3318, k := 474, d := 2845, e := 1584, g := 16, m := 420929
        fieldBits := 128, fieldOrder := 0
        openings := 132, targetBits := 125
        maskThreshold := 1728, hahnMask := HahnMask.v7Hash2 } }

theorem v7Hash2_v1_parameters : v7Hash2_v1.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, by change (decide (1728 ≤ Nat.sqrt (3318 * 947) + 1) && decide (947 < 1728) && (decide (Nat.sqrt (3318 * 947) + 1 ≤ 1728) || CodingTheory.HahnDelsarte.certificateValid 3318 1728 947 HahnMask.v7Hash2)) = true; rw [HahnMask.v7Hash2_valid]; decide +kernel, ?_⟩
  exact v7Hash2_v1.certificate.conditions_of_checked
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

theorem v7Hash2_v1_compressed_bound :
    v7Hash2_v1.compressedBound ≤ (1 : ℚ) / 2 ^ v7Hash2_v1.certificate.targetBits := by native_decide

theorem v7Hash2_v1_bound :
    v7Hash2_v1.bound ≤ (1 : ℚ) / 2 ^ v7Hash2_v1.certificate.targetBits := by
  rw [← Result.compressedBound_eq]; exact v7Hash2_v1_compressed_bound

def v7Hash2_v1_certified : CertifiedResult :=
  ⟨v7Hash2_v1, v7Hash2_v1_parameters, v7Hash2_v1_bound⟩

def v7Hash2_v1_extraction := @CertifiedResult.v1_extraction v7Hash2_v1_certified rfl

def v7Hash2_v1_interactive := @CertifiedResult.v1_interactive v7Hash2_v1_certified rfl

def v7Hash2_v1_uniform_envelope := @CertifiedResult.v1_uniform_envelope v7Hash2_v1_certified rfl

def v7Hash3_v2 : Result :=
  { variant := .v2, route := .johnson, etaBits := 0, adaptiveEta := true
    certificate :=
      { n := 3352, k := 478, d := 2875, e := 1733, g := 24, m := 9793967305
        fieldBits := 128, fieldOrder := 0
        openings := 132, targetBits := 126 } }

theorem v7Hash3_v2_parameters : v7Hash3_v2.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, by trivial, ?_⟩
  change v7Hash3_v2.certificate.inverseJohnsonConditions
    (v7Hash3_v2.etaDenominators (v7Hash3_v2.certificate.n - v7Hash3_v2.certificate.e))
    v7Hash3_v2.etaDenominators = true
  native_decide

theorem v7Hash3_v2_compressed_bound :
    v7Hash3_v2.compressedBound ≤ (1 : ℚ) / 2 ^ v7Hash3_v2.certificate.targetBits := by native_decide

theorem v7Hash3_v2_bound :
    v7Hash3_v2.bound ≤ (1 : ℚ) / 2 ^ v7Hash3_v2.certificate.targetBits := by
  rw [← Result.compressedBound_eq]; exact v7Hash3_v2_compressed_bound

def v7Hash3_v2_certified : CertifiedResult :=
  ⟨v7Hash3_v2, v7Hash3_v2_parameters, v7Hash3_v2_bound⟩

def v7Hash3_v2_extraction := @CertifiedResult.v2_extraction v7Hash3_v2_certified rfl

def v7Hash3_v2_interactive := @CertifiedResult.v2_interactive v7Hash3_v2_certified rfl

def v7Hash3_v2_uniform_envelope := @CertifiedResult.v2_uniform_envelope v7Hash3_v2_certified rfl

def v7Hash3_v3 : Result := { v7Hash3_v2 with variant := .v3 }

theorem v7Hash3_v3_parameters : v7Hash3_v3.ParametersValid := v7Hash3_v2_parameters

theorem v7Hash3_v3_compressed_bound :
    v7Hash3_v3.compressedBound ≤ (1 : ℚ) / 2 ^ v7Hash3_v3.certificate.targetBits := v7Hash3_v2_compressed_bound

theorem v7Hash3_v3_bound :
    v7Hash3_v3.bound ≤ (1 : ℚ) / 2 ^ v7Hash3_v3.certificate.targetBits := by
  rw [← Result.compressedBound_eq]; exact v7Hash3_v3_compressed_bound

def v7Hash3_v3_certified : CertifiedResult :=
  ⟨v7Hash3_v3, v7Hash3_v3_parameters, v7Hash3_v3_bound⟩

def v7Hash3_v3_extraction := @CertifiedResult.v3_extraction v7Hash3_v3_certified rfl

def v7Hash3_v3_interactive := @CertifiedResult.v3_interactive v7Hash3_v3_certified rfl

def v7Hash3_v3_uniform_envelope := @CertifiedResult.v3_uniform_envelope v7Hash3_v3_certified rfl

def v7Hash3_v1 : Result :=
  { variant := .v1, route := .triples, etaBits := 0, adaptiveEta := false
    certificate :=
      { n := 3352, k := 478, d := 2875, e := 1601, g := 16, m := 310355
        fieldBits := 128, fieldOrder := 0
        openings := 132, targetBits := 125
        maskThreshold := 1744, hahnMask := HahnMask.v7Hash3 } }

theorem v7Hash3_v1_parameters : v7Hash3_v1.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, by change (decide (1744 ≤ Nat.sqrt (3352 * 955) + 1) && decide (955 < 1744) && (decide (Nat.sqrt (3352 * 955) + 1 ≤ 1744) || CodingTheory.HahnDelsarte.certificateValid 3352 1744 955 HahnMask.v7Hash3)) = true; rw [HahnMask.v7Hash3_valid]; decide +kernel, ?_⟩
  exact v7Hash3_v1.certificate.conditions_of_checked
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

theorem v7Hash3_v1_compressed_bound :
    v7Hash3_v1.compressedBound ≤ (1 : ℚ) / 2 ^ v7Hash3_v1.certificate.targetBits := by native_decide

theorem v7Hash3_v1_bound :
    v7Hash3_v1.bound ≤ (1 : ℚ) / 2 ^ v7Hash3_v1.certificate.targetBits := by
  rw [← Result.compressedBound_eq]; exact v7Hash3_v1_compressed_bound

def v7Hash3_v1_certified : CertifiedResult :=
  ⟨v7Hash3_v1, v7Hash3_v1_parameters, v7Hash3_v1_bound⟩

def v7Hash3_v1_extraction := @CertifiedResult.v1_extraction v7Hash3_v1_certified rfl

def v7Hash3_v1_interactive := @CertifiedResult.v1_interactive v7Hash3_v1_certified rfl

def v7Hash3_v1_uniform_envelope := @CertifiedResult.v1_uniform_envelope v7Hash3_v1_certified rfl

def v7Hash4_v2 : Result :=
  { variant := .v2, route := .johnson, etaBits := 0, adaptiveEta := true
    certificate :=
      { n := 3436, k := 490, d := 2947, e := 1777, g := 24, m := 10042792941
        fieldBits := 128, fieldOrder := 0
        openings := 132, targetBits := 126 } }

theorem v7Hash4_v2_parameters : v7Hash4_v2.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, by trivial, ?_⟩
  change v7Hash4_v2.certificate.inverseJohnsonConditions
    (v7Hash4_v2.etaDenominators (v7Hash4_v2.certificate.n - v7Hash4_v2.certificate.e))
    v7Hash4_v2.etaDenominators = true
  native_decide

theorem v7Hash4_v2_compressed_bound :
    v7Hash4_v2.compressedBound ≤ (1 : ℚ) / 2 ^ v7Hash4_v2.certificate.targetBits := by native_decide

theorem v7Hash4_v2_bound :
    v7Hash4_v2.bound ≤ (1 : ℚ) / 2 ^ v7Hash4_v2.certificate.targetBits := by
  rw [← Result.compressedBound_eq]; exact v7Hash4_v2_compressed_bound

def v7Hash4_v2_certified : CertifiedResult :=
  ⟨v7Hash4_v2, v7Hash4_v2_parameters, v7Hash4_v2_bound⟩

def v7Hash4_v2_extraction := @CertifiedResult.v2_extraction v7Hash4_v2_certified rfl

def v7Hash4_v2_interactive := @CertifiedResult.v2_interactive v7Hash4_v2_certified rfl

def v7Hash4_v2_uniform_envelope := @CertifiedResult.v2_uniform_envelope v7Hash4_v2_certified rfl

def v7Hash4_v3 : Result := { v7Hash4_v2 with variant := .v3 }

theorem v7Hash4_v3_parameters : v7Hash4_v3.ParametersValid := v7Hash4_v2_parameters

theorem v7Hash4_v3_compressed_bound :
    v7Hash4_v3.compressedBound ≤ (1 : ℚ) / 2 ^ v7Hash4_v3.certificate.targetBits := v7Hash4_v2_compressed_bound

theorem v7Hash4_v3_bound :
    v7Hash4_v3.bound ≤ (1 : ℚ) / 2 ^ v7Hash4_v3.certificate.targetBits := by
  rw [← Result.compressedBound_eq]; exact v7Hash4_v3_compressed_bound

def v7Hash4_v3_certified : CertifiedResult :=
  ⟨v7Hash4_v3, v7Hash4_v3_parameters, v7Hash4_v3_bound⟩

def v7Hash4_v3_extraction := @CertifiedResult.v3_extraction v7Hash4_v3_certified rfl

def v7Hash4_v3_interactive := @CertifiedResult.v3_interactive v7Hash4_v3_certified rfl

def v7Hash4_v3_uniform_envelope := @CertifiedResult.v3_uniform_envelope v7Hash4_v3_certified rfl

def v7Hash4_v1 : Result :=
  { variant := .v1, route := .triples, etaBits := 0, adaptiveEta := false
    certificate :=
      { n := 3436, k := 490, d := 2947, e := 1642, g := 16, m := 4467784
        fieldBits := 128, fieldOrder := 0
        openings := 132, targetBits := 125
        maskThreshold := 1788, hahnMask := HahnMask.v7Hash4 } }

theorem v7Hash4_v1_parameters : v7Hash4_v1.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, by change (decide (1788 ≤ Nat.sqrt (3436 * 979) + 1) && decide (979 < 1788) && (decide (Nat.sqrt (3436 * 979) + 1 ≤ 1788) || CodingTheory.HahnDelsarte.certificateValid 3436 1788 979 HahnMask.v7Hash4)) = true; rw [HahnMask.v7Hash4_valid]; decide +kernel, ?_⟩
  exact v7Hash4_v1.certificate.conditions_of_checked
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

theorem v7Hash4_v1_compressed_bound :
    v7Hash4_v1.compressedBound ≤ (1 : ℚ) / 2 ^ v7Hash4_v1.certificate.targetBits := by native_decide

theorem v7Hash4_v1_bound :
    v7Hash4_v1.bound ≤ (1 : ℚ) / 2 ^ v7Hash4_v1.certificate.targetBits := by
  rw [← Result.compressedBound_eq]; exact v7Hash4_v1_compressed_bound

def v7Hash4_v1_certified : CertifiedResult :=
  ⟨v7Hash4_v1, v7Hash4_v1_parameters, v7Hash4_v1_bound⟩

def v7Hash4_v1_extraction := @CertifiedResult.v1_extraction v7Hash4_v1_certified rfl

def v7Hash4_v1_interactive := @CertifiedResult.v1_interactive v7Hash4_v1_certified rfl

def v7Hash4_v1_uniform_envelope := @CertifiedResult.v1_uniform_envelope v7Hash4_v1_certified rfl

/-- The larger-radius V1 flat certificates still give at most two committed lifts
at each of the four deployed hash geometries. -/
theorem v7Hash_v1_flat_listSize_two :
    v7Hash1_v1.certificate.listSize ≤ 2 ∧
    v7Hash2_v1.certificate.listSize ≤ 2 ∧
    v7Hash3_v1.certificate.listSize ≤ 2 ∧
    v7Hash4_v1.certificate.listSize ≤ 2 := by
  native_decide

end Ligero.Examples.Grid.LongfellowProfiledExtraction.Optimized
