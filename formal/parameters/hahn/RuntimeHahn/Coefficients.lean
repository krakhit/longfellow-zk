import RuntimeHahn.HahnPolynomial

/-! Exact coefficient arithmetic for the Hahn certificate checker.  The
evaluation homomorphism is proved once; individual identities are checked
by reduction of closed coefficient lists rather than symbolic expansion. -/

namespace CodingTheory.HahnDelsarte.Fast

namespace Coefficients

def add : List ℚ → List ℚ → List ℚ
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: add p q

def scale (a : ℚ) (p : List ℚ) : List ℚ := p.map (a * ·)

theorem eval_add (p q : List ℚ) (x : ℚ) :
    eval (add p q) x = eval p x + eval q x := by
  induction p generalizing q with
  | nil => simp [add, eval]
  | cons a p ih =>
    cases q with
    | nil => simp [add, eval]
    | cons b q => simp only [add, eval, ih]; ring

theorem eval_scale (a : ℚ) (p : List ℚ) (x : ℚ) :
    eval (scale a p) x = a * eval p x := by
  induction p with
  | nil => simp [scale, eval]
  | cons b p ih =>
    change a * b + x * eval (scale a p) x = a * (b + x * eval p x)
    rw [ih]
    ring

end Coefficients
end CodingTheory.HahnDelsarte.Fast
