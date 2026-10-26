import LfzkV1.GradedCost
import LfzkV1.CertifiedHahn

/-!
# Graded terminal budgets for the signature sides

The v7 Hahn/Delsarte signature contribution is small relative to the hash
sides. A single-step curve at the certified
query cover reproduces the registered challenge and query bounds, while
using the same extraction-first potential interface as the hash curves.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace LfzkV1.GradedSignature

open Finset LigeroFamily LigeroFamily.PotentialProfile
  LigeroFamily.PolicyDoublyProfiledSoundnessClassifier
  LfzkV1.CertifiedV1

def row : Row := v7SigHahn

def curve : Curve row.params.row.n :=
  stepCurve _ (row.params.row.queryCover + 1) (by omega)

abbrev challengeCost : ℚ := LfzkV1.GradedCost.challenge row curve

abbrev queryCost : ℚ := LfzkV1.GradedCost.query row curve

/-- The challenge cost is no larger than the registered two profile tails. -/
theorem challengeCost_le :
    challengeCost ≤ row.params.row.fail + row.params.row.arith := by native_decide

/-- The residual query cost is no larger than the registered cover. -/
theorem queryCost_le : queryCost ≤ row.params.row.cover := by native_decide

theorem terminalCost_le_registered :
    challengeCost + queryCost ≤ row.params.ligeroDensity := by
  have hc := challengeCost_le
  have hq := queryCost_le
  change challengeCost + queryCost ≤
    (row.params.row.fail + row.params.row.arith) + row.params.row.cover
  linarith

end LfzkV1.GradedSignature
