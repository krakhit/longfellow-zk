import LfzkV1.GradedV7Hash
import LfzkV1.GradedSignature
import LfzkV1.RbrZkPotentialTwoField

/-!
# Graded two-field density certificates

The density bounds apply to any balanced combined challenge alphabet.  The
adaptive arithmetic retains the deployed transcript-query and Merkle terms.
The compiled extraction theorem and its generic density comparison are
separate from these closed row checks.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace LfzkV1.GradedCoreGrid

open LfzkV1.CertifiedV1 LfzkV1.NizkZk

def v7Core (i : Fin 4) : ℚ :=
  let H := LfzkV1.GradedV7Hash.row i
  (H.cardCand : ℚ) * zkFieldDensity H (LfzkV1.SoundnessAudit.v7HashLogv i) +
    LfzkV1.GradedV7Hash.challengeCost i + LfzkV1.GradedV7Hash.queryCost i +
    (v7SigHahn.cardCand : ℚ) * zkFieldDensity v7SigHahn 8 +
    LfzkV1.GradedSignature.challengeCost +
    LfzkV1.GradedSignature.queryCost + (4 : ℚ) / 2 ^ 128

/-- The four v7 two-field constant cores fit within 115 bits. -/
theorem v7Core_le_115 (i : Fin 4) :
    v7Core i ≤ (1 : ℚ) / 2 ^ 115 := by
  have hh := LfzkV1.GradedV7Hash.terminalCost_le i
  have hs := LfzkV1.GradedSignature.terminalCost_le_registered
  have hn :
      let H := LfzkV1.GradedV7Hash.row i
      (H.cardCand : ℚ) * zkFieldDensity H (LfzkV1.SoundnessAudit.v7HashLogv i) +
        (LfzkV1.GradedV7Hash.terminalNumerator i : ℚ) / 2 ^ 128 +
        (v7SigHahn.cardCand : ℚ) * zkFieldDensity v7SigHahn 8 +
        v7SigHahn.params.ligeroDensity + (4 : ℚ) / 2 ^ 128 ≤
          (1 : ℚ) / 2 ^ 115 := by
    fin_cases i <;> native_decide
  change LfzkV1.GradedSignature.challengeCost +
      LfzkV1.GradedSignature.queryCost ≤
        v7SigHahn.params.ligeroDensity at hs
  dsimp only at hn
  dsimp only [v7Core]
  linarith

/-- Alphabet-independent density upper bound for the four v7 pairs. -/
def v7DensityUpper (i : Fin 4) : ℚ :=
  let H := LfzkV1.GradedV7Hash.row i
  (4 : ℚ) / 2 ^ 128 +
    (H.cardCand : ℚ) * zkFieldDensity H
      (LfzkV1.SoundnessAudit.v7HashLogv i) +
    (LfzkV1.GradedV7Hash.challengeNumerator i : ℚ) / 2 ^ 128 +
    (LfzkV1.GradedV7Hash.queryNumerator i : ℚ) / 2 ^ 128 +
    (v7SigHahn.cardCand : ℚ) * zkFieldDensity v7SigHahn 8 +
    v7SigHahn.params.row.fail + v7SigHahn.params.row.arith +
    v7SigHahn.params.row.cover

theorem v7DensityUpper_le_115 (i : Fin 4) :
    v7DensityUpper i ≤ (1 : ℚ) / 2 ^ 115 := by
  fin_cases i <;> native_decide

/-- The graded tails remain below the registered worst-slot coefficient,
which is the premise of the alphabet-independent maximum theorem. -/
theorem v7GradedCosts_le_coefficient (i : Fin 4) :
    let H := LfzkV1.GradedV7Hash.row i
    (LfzkV1.GradedV7Hash.challengeNumerator i : ℚ) / 2 ^ 128 ≤
      H.zkCoefficient (LfzkV1.SoundnessAudit.v7HashLogv i) ∧
    (LfzkV1.GradedV7Hash.queryNumerator i : ℚ) / 2 ^ 128 ≤
      H.zkCoefficient (LfzkV1.SoundnessAudit.v7HashLogv i) ∧
    v7SigHahn.params.row.fail + v7SigHahn.params.row.arith ≤
      v7SigHahn.zkCoefficient 8 ∧
    v7SigHahn.params.row.cover ≤ v7SigHahn.zkCoefficient 8 := by
  fin_cases i <;> native_decide

/-- The alphabet-independent v7 constant fits under the previously
certified adaptive-hash arithmetic envelope. -/
theorem v7DensityUpper_le_registered (i : Fin 4) :
    let H := LfzkV1.GradedV7Hash.row i
    v7DensityUpper i ≤
      zkCoreAt H (LfzkV1.SoundnessAudit.v7HashLogv i) H.cardCand +
      zkCoreAt v7SigHahn 8 v7SigHahn.cardCand + (4 : ℚ) / 2 ^ 128 := by
  fin_cases i <;> native_decide

/-- Full v7 density arithmetic with the deployed adaptive Merkle term. -/
theorem v7DensityRhs_le_115 (i : Fin 4) (N tA : ℕ)
    (htA : tA ≤ 2 ^ 115) :
    let H := LfzkV1.GradedV7Hash.row i
    let fc := 2 * H.params.row.n + 2 * v7SigHahn.params.row.n
    let L := LfzkV1.NizkAdaptiveTwoField.len2 H v7SigHahn
    let K := max (max (H.zkCoefficient
      (LfzkV1.SoundnessAudit.v7HashLogv i))
      (v7SigHahn.zkCoefficient 8)) ((4 : ℚ) / 2 ^ 128)
    v7DensityUpper i + N * K +
      2 * (Bcs.AdaptiveCommit.adaptiveNumerator fc tA (L + N) : ℚ) /
        2 ^ 256 ≤ (1 + N + tA : ℚ) / 2 ^ 115 := by
  dsimp only
  have hc := v7DensityUpper_le_registered i
  dsimp only at hc
  have hregistered := LfzkV1.SoundnessAudit.hahn_twofield_linear_rhs i N tA htA
  dsimp only at hregistered
  calc
    v7DensityUpper i + N *
        max (max ((LfzkV1.GradedV7Hash.row i).zkCoefficient
          (LfzkV1.SoundnessAudit.v7HashLogv i))
          (v7SigHahn.zkCoefficient 8)) ((4 : ℚ) / 2 ^ 128) +
        2 * (Bcs.AdaptiveCommit.adaptiveNumerator
          (2 * (LfzkV1.GradedV7Hash.row i).params.row.n +
            2 * v7SigHahn.params.row.n) tA
          (LfzkV1.NizkAdaptiveTwoField.len2 (LfzkV1.GradedV7Hash.row i)
            v7SigHahn + N) : ℚ) / 2 ^ 256
      ≤ zkCoreAt (LfzkV1.GradedV7Hash.row i)
          (LfzkV1.SoundnessAudit.v7HashLogv i)
          (LfzkV1.GradedV7Hash.row i).cardCand +
          zkCoreAt v7SigHahn 8 v7SigHahn.cardCand + (4 : ℚ) / 2 ^ 128 +
          N * max (max ((LfzkV1.GradedV7Hash.row i).zkCoefficient
            (LfzkV1.SoundnessAudit.v7HashLogv i))
            (v7SigHahn.zkCoefficient 8)) ((4 : ℚ) / 2 ^ 128) +
          2 * (Bcs.AdaptiveCommit.adaptiveNumerator
            (2 * (LfzkV1.GradedV7Hash.row i).params.row.n +
              2 * v7SigHahn.params.row.n) tA
            (LfzkV1.NizkAdaptiveTwoField.len2 (LfzkV1.GradedV7Hash.row i)
              v7SigHahn + N) : ℚ) / 2 ^ 256 := by linarith
    _ ≤ (651 : ℚ) / (1000 * 2 ^ 115) +
          N * ((1 : ℚ) / 2 ^ 117) + tA * ((1 : ℚ) / 2 ^ 138) :=
        hregistered
    _ ≤ (1 + N + tA : ℚ) / 2 ^ 115 := by
      have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg _
      have ht : (0 : ℚ) ≤ tA := Nat.cast_nonneg _
      nlinarith

/-- The exact compiled hash-answer budget for a v7 geometry, kept symbolic
in the combined challenge alphabet and MAC decoder multiplicity. -/
def v7GradedBudget (i : Fin 4) (cardC kmac N : ℕ) : ℚ :=
  LfzkV1.NizkZkDeployedHash.gradedCombinedBudget
    (LfzkV1.GradedV7Hash.row i) v7SigHahn
    (LfzkV1.SoundnessAudit.v7HashLogv i) 8 cardC N
    (4 * kmac : ℚ)
    ((LfzkV1.GradedV7Hash.challengeNumerator i : ℚ) / 2 ^ 128)
    ((LfzkV1.GradedV7Hash.queryNumerator i : ℚ) / 2 ^ 128)
    (v7SigHahn.params.row.fail + v7SigHahn.params.row.arith)
    v7SigHahn.params.row.cover

theorem v7GradedBudget_le_density (i : Fin 4) (cardC kmac N : ℕ)
    (hC : 0 < cardC) (hmac : kmac * 2 ^ 128 ≤ cardC) :
    v7GradedBudget i cardC kmac N ≤
      v7DensityUpper i + N *
        max (max ((LfzkV1.GradedV7Hash.row i).zkCoefficient
          (LfzkV1.SoundnessAudit.v7HashLogv i))
          (v7SigHahn.zkCoefficient 8)) ((4 : ℚ) / 2 ^ 128) := by
  have hF₁ : 0 < (LfzkV1.GradedV7Hash.row i).params.row.fieldSize := by
    fin_cases i <;> decide
  have hF₂ : 0 < v7SigHahn.params.row.fieldSize := by native_decide
  obtain ⟨h₁c, h₁q, h₂c, h₂q⟩ := v7GradedCosts_le_coefficient i
  have hb₂c : 0 ≤ v7SigHahn.params.row.fail +
      v7SigHahn.params.row.arith := by native_decide
  have hb₂q : 0 ≤ v7SigHahn.params.row.cover := by native_decide
  have hb₁c : 0 ≤
      (LfzkV1.GradedV7Hash.challengeNumerator i : ℚ) / 2 ^ 128 := by
    exact div_nonneg (Nat.cast_nonneg _) (by positivity)
  have hb₁q : 0 ≤
      (LfzkV1.GradedV7Hash.queryNumerator i : ℚ) / 2 ^ 128 := by
    exact div_nonneg (Nat.cast_nonneg _) (by positivity)
  have h := LfzkV1.NizkZkDeployedHash.gradedCombinedBudget_le_density
    (LfzkV1.GradedV7Hash.row i) v7SigHahn
    (LfzkV1.SoundnessAudit.v7HashLogv i) 8 cardC (2 ^ 128) 2 2 kmac N
    hC (by positivity) hF₁ hF₂ hmac
    ((LfzkV1.GradedV7Hash.challengeNumerator i : ℚ) / 2 ^ 128)
    ((LfzkV1.GradedV7Hash.queryNumerator i : ℚ) / 2 ^ 128)
    (v7SigHahn.params.row.fail + v7SigHahn.params.row.arith)
    v7SigHahn.params.row.cover
    hb₁c hb₁q hb₂c hb₂q h₁c h₁q h₂c h₂q
  unfold v7GradedBudget v7DensityUpper
  dsimp only
  convert h using 1 <;> push_cast <;> ring_nf

/-- The exact v7 numerator of the compiled graded extraction theorem,
including adaptive Merkle accounting, has the 115-bit T-security envelope. -/
theorem v7GradedBudgetRhs_le_115 (i : Fin 4)
    (cardC kmac N tA : ℕ) (hC : 0 < cardC)
    (hmac : kmac * 2 ^ 128 ≤ cardC) (htA : tA ≤ 2 ^ 115) :
    let H := LfzkV1.GradedV7Hash.row i
    let fc := 2 * H.params.row.n + 2 * v7SigHahn.params.row.n
    let L := LfzkV1.NizkAdaptiveTwoField.len2 H v7SigHahn
    v7GradedBudget i cardC kmac N +
      2 * (Bcs.AdaptiveCommit.adaptiveNumerator fc tA (L + N) : ℚ) /
        2 ^ 256 ≤ (1 + N + tA : ℚ) / 2 ^ 115 := by
  dsimp only
  have hb := v7GradedBudget_le_density i cardC kmac N hC hmac
  have hr := v7DensityRhs_le_115 i N tA htA
  dsimp only at hr
  linarith

/-- With a positive transcript-query budget, the graded v7 extraction
numerator fits the 116-bit T-security envelope.  The zero-query case needs
the flat terminal-pair argument rather than this separate-slot envelope. -/
theorem v7GradedBudgetRhs_le_116_of_pos_queries (i : Fin 4)
    (cardC kmac N tA : ℕ) (hC : 0 < cardC)
    (hmac : kmac * 2 ^ 128 ≤ cardC) (hN : 0 < N)
    (htA : tA ≤ 2 ^ 116) :
    let H := LfzkV1.GradedV7Hash.row i
    let fc := 2 * H.params.row.n + 2 * v7SigHahn.params.row.n
    let L := LfzkV1.NizkAdaptiveTwoField.len2 H v7SigHahn
    v7GradedBudget i cardC kmac N +
      2 * (Bcs.AdaptiveCommit.adaptiveNumerator fc tA (L + N) : ℚ) /
        2 ^ 256 ≤ (1 + N + tA : ℚ) / 2 ^ 116 := by
  dsimp only
  have hb := v7GradedBudget_le_density i cardC kmac N hC hmac
  have hc := v7DensityUpper_le_registered i
  have hp := LfzkV1.SoundnessAudit.hahn_twofield_116_of_pos_queries_extended
    i N tA hN htA
  dsimp only at hc hp
  simp only [LfzkV1.GradedV7Hash.row] at hb hc ⊢
  linarith

end LfzkV1.GradedCoreGrid
