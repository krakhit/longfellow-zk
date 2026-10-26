import RuntimeHahn.Coefficients
import RuntimeHahn.IntegralKernel

/-! Combine checked Hahn identities and check certificate signs with integer Horner arithmetic. -/

namespace CodingTheory.HahnDelsarte.Fast
open Finset

def KernelsCorrect (n w : ℕ) : ℕ → List (List ℚ) → Prop
  | _, [] => True
  | k, p :: ps => (∀ x, kernel n w k x = eval p x) ∧ KernelsCorrect n w (k + 1) ps

def weightedCoefficients (cs : List ℕ) : ℕ → List (List ℚ) → List ℚ
  | _, [] => []
  | k, p :: ps => Coefficients.add (Coefficients.scale (cs.getD k 0) p)
      (weightedCoefficients cs (k + 1) ps)

theorem eval_weightedCoefficients (n w : ℕ) (cs : List ℕ) (ps : List (List ℚ))
    (start : ℕ) (h : KernelsCorrect n w start ps) (x : ℚ) :
    eval (weightedCoefficients cs start ps) x =
      ∑ i ∈ range ps.length, (cs.getD (start + i) 0 : ℚ) * kernel n w (start + i) x := by
  induction ps generalizing start with
  | nil => simp [weightedCoefficients, eval]
  | cons p ps ih =>
    rw [weightedCoefficients, Coefficients.eval_add, Coefficients.eval_scale, ← h.1 x,
      ih (start + 1) h.2]
    simp only [List.length_cons, sum_range_succ', Nat.add_zero]
    simp only [Nat.add_left_comm, add_comm]

def certificateCoefficients (cs : List ℕ) (ps : List (List ℚ)) : List ℚ :=
  Coefficients.add [(cs.headD 0 : ℚ)] (weightedCoefficients cs 1 ps)

theorem polynomial_eq_of_kernels (n w : ℕ) (cs : List ℕ) (ps : List (List ℚ))
    (p : List ℚ) (hlen : ps.length = cs.length - 1)
    (h : KernelsCorrect n w 1 ps) (hc : certificateCoefficients cs ps = p) (x : ℚ) :
    polynomial n w cs x = eval p x := by
  rw [← hc, certificateCoefficients, Coefficients.eval_add, eval_weightedCoefficients n w cs ps 1 h]
  simp only [eval, mul_zero, add_zero, polynomial, hlen]
  congr 1
  have hs (m : ℕ) : (∑ i ∈ range m, (cs.getD (1 + i) 0 : ℚ) * kernel n w (1 + i) x) =
      ∑ i ∈ Icc 1 m, (cs.getD i 0 : ℚ) * kernel n w i x := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_range_succ, sum_Icc_succ_top (by omega), ih]
      simp only [Nat.add_comm]
  exact (hs _).symm

def signsCheck (n w lam : ℕ) (p : List ℤ) : Bool :=
  (List.range (lam + 1)).all fun t =>
    decide (n + t < 2 * w) || decide (Integral.eval p t ≤ 0)

theorem certificate_of_integral (n w lam : ℕ) (cs : List ℕ) (p : List ℤ) (d : ℕ)
    (hw : lam ≤ w) (hd : 0 < d)
    (heq : ∀ x, polynomial n w cs x = eval (p.map fun a : ℤ => (a : ℚ) / d) x)
    (hpos : 0 < cs.headD 0) (hneg : signsCheck n w lam p = true) :
    certificateValid n w lam cs = true := by
  simp only [certificateValid, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_range, Bool.or_eq_true]
  refine ⟨hpos, fun t ht => ?_⟩
  have h := List.all_eq_true.mp hneg t (List.mem_range.mpr ht)
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · exact Or.inl h
  · by_cases hn : n + t < 2 * w
    · exact Or.inl hn
    · apply Or.inr
      rw [← polynomial_nat n w cs t (by omega) (by omega), heq, Identity.eval_div]
      have hi : (Integral.eval p t : ℚ) ≤ 0 := by exact_mod_cast h
      rw [Integral.cast_eval] at hi
      exact div_nonpos_of_nonpos_of_nonneg (by simpa using hi) (by positivity)

end CodingTheory.HahnDelsarte.Fast
