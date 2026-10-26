import LfzkV2.Soundness

/-!
# The V2 effective circuit tensor

Ordinary coefficients are weighted by the current output weights. Each assertion
has its own coefficient, replacing the entire weighted coefficient. An assertion
index denotes an occurrence in the sparse circuit, so duplicate assertions are
not merged. Dense tensors also represent zero padding of non-power-of-two tables.
-/

namespace LfzkV2

open SumcheckV2 Classical

variable {F Wire Output Assertion : Type} [Field F]
variable [Fintype Wire] [Fintype Output] [Fintype Assertion]

def quadratic (K : Wire → Wire → F) (w : Wire → F) : F :=
  ∑ l, ∑ r, K l r * w l * w r

theorem quadratic_eq_dot (K : Wire → Wire → F) (w : Wire → F) :
    quadratic K w = dot (bindRight K w) w := by
  simp only [quadratic, dot, bindRight, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem quadratic_add (K L : Wire → Wire → F) (w : Wire → F) :
    quadratic (fun l r => K l r + L l r) w = quadratic K w + quadratic L w := by
  simp [quadratic, add_mul, Finset.sum_add_distrib]

theorem quadratic_weighted_sum {ι : Type} [Fintype ι]
    (weights : ι → F) (K : ι → Wire → Wire → F) (w : Wire → F) :
    quadratic (fun l r => ∑ i, weights i * K i l r) w =
      dot weights (fun i => quadratic (K i) w) := by
  simp only [quadratic, dot, Finset.sum_mul, Finset.mul_sum]
  calc
    (∑ l, ∑ r, ∑ i, weights i * K i l r * w l * w r) =
        ∑ l, ∑ i, ∑ r, weights i * K i l r * w l * w r := by
          apply Finset.sum_congr rfl
          intro l _
          exact Finset.sum_comm
    _ = ∑ i, ∑ l, ∑ r, weights i * K i l r * w l * w r := Finset.sum_comm
    _ = _ := by simp only [mul_assoc]

structure CircuitLayer (Output Wire Assertion F : Type) where
  ordinary : Output → Wire → Wire → F
  left : Assertion → Wire
  right : Assertion → Wire

namespace CircuitLayer

def outputs (layer : CircuitLayer Output Wire Assertion F) (w : Wire → F) : Output → F :=
  fun g => quadratic (layer.ordinary g) w

def residuals (layer : CircuitLayer Output Wire Assertion F) (w : Wire → F) : Assertion → F :=
  fun a => w (layer.left a) * w (layer.right a)

noncomputable def assertionKernel (layer : CircuitLayer Output Wire Assertion F)
    (a : Assertion) (l r : Wire) : F :=
  if l = layer.left a ∧ r = layer.right a then 1 else 0

omit [Fintype Output] [Fintype Assertion] in
theorem quadratic_assertion (layer : CircuitLayer Output Wire Assertion F) (w : Wire → F)
    (a : Assertion) : quadratic (layer.assertionKernel a) w = layer.residuals w a := by
  classical
  simp [quadratic, assertionKernel, residuals, ite_and]

noncomputable def effective (layer : CircuitLayer Output Wire Assertion F)
    (weights : Output → F) (beta : Assertion → F) (l r : Wire) : F :=
  (∑ g, weights g * layer.ordinary g l r) +
    ∑ a, beta a * layer.assertionKernel a l r

/-- This identity also holds for a witness violating assertions. Such a witness
changes the effective true claim by its randomly weighted assertion residuals. -/
theorem effective_truth (layer : CircuitLayer Output Wire Assertion F)
    (weights : Output → F) (beta : Assertion → F) (w : Wire → F) :
    dot (bindRight (layer.effective weights beta) w) w =
      dot weights (layer.outputs w) + dot beta (layer.residuals w) := by
  rw [← quadratic_eq_dot]
  unfold effective
  rw [quadratic_add, quadratic_weighted_sum, quadratic_weighted_sum]
  simp only [quadratic_assertion]
  rfl

/-- Valid assertions contribute zero for every challenge, including zero challenges. -/
theorem effective_truth_of_valid (layer : CircuitLayer Output Wire Assertion F)
    (weights : Output → F) (beta : Assertion → F) (w : Wire → F)
    (hvalid : ∀ a, layer.residuals w a = 0) :
    dot (bindRight (layer.effective weights beta) w) w = dot weights (layer.outputs w) := by
  rw [effective_truth]
  simp [dot, hvalid]

end CircuitLayer

/-- A layer model with the ordinary incoming sum and all assertion occurrences.
`mixed_truth` is instantiated by `CircuitLayer.effective_truth`, not by assuming
the assertions are satisfied. -/
structure AssertedModel (F : Type) [Field F] extends LayerModel F where
  incoming : F
  assertions : ℕ
  residuals : Fin assertions → F
  beta : Fin assertions → F
  mixed_truth : toLayerModel.truth = incoming + dot beta residuals

noncomputable def CircuitLayer.model {n : ℕ} {A : ℕ}
    (layer : CircuitLayer Output (Cube n) (Fin A) F) (weights : Output → F)
    (beta : Fin A → F) (w : Cube n → F) (point : Fin n → F) : AssertedModel F where
  logSize := n
  kernel := layer.effective weights beta
  wires := w
  point := point
  incoming := dot weights (layer.outputs w)
  assertions := A
  residuals := layer.residuals w
  beta := beta
  mixed_truth := layer.effective_truth weights beta w

end LfzkV2
