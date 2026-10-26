import RuntimeHahn.PolynomialIdentity

/-! Kernel-checked integer evaluation of Hahn polynomials. A supplied common
denominator clears the rational weights. Their cross-products are checked
independently, then a degree-k identity is checked at the k+1 distinct points
w, w-1, ..., w-k. `kernel_eq_eval` proves that these finite checks imply the
identity at every rational argument. -/

namespace CodingTheory.HahnDelsarte.Fast.Integral

open Finset

def sum : ℕ → (ℕ → ℤ) → ℤ
  | 0, _ => 0
  | k + 1, f => sum k f + f k

def kernel (n w k t : ℕ) (weights : List ℤ) : ℤ :=
  sum (k + 1) fun i => weights.getD i 0 *
    sum (i + 1) fun a =>
      let p := Nat.fast_choose t a * Nat.fast_choose (w - t) (i - a)
      if p = 0 then 0 else (p : ℤ) *
        sum (k - i + 1) fun c =>
          (Nat.fast_choose (w - t) c * Nat.fast_choose (n + t - 2 * w) (k - i - c) : ℕ) *
            weights.getD (a + c) 0

def eval : List ℤ → ℤ → ℤ
  | [], _ => 0
  | a :: p, x => a + x * eval p x

def check (n w k : ℕ) (weights : List ℤ) (denom : ℕ)
    (coeffs : List ℤ) (polyDenom : ℕ) : Bool :=
  (List.range (k + 1)).all fun t =>
    kernel n w k (w - t) weights * polyDenom == eval coeffs (w - t : ℕ) * (denom : ℤ)^2

def weightsCheck (n w k d : ℕ) (weights : List ℤ) : Bool :=
  (List.range (k + 1)).all fun i =>
    weights.getD i 0 * (Nat.fast_choose w i : ℤ) ==
      (-1 : ℤ)^i * Nat.fast_choose (n + i - (w + k)) i * d

theorem sum_eq (n : ℕ) (f : ℕ → ℤ) : sum n f = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp [sum]
  | succ n ih => simp [sum, ih, sum_range_succ]

theorem weightsCheck_sound (n w k d : ℕ) (weights : List ℤ) (hk : k ≤ w)
    (h : weightsCheck n w k d weights = true) (i : ℕ) (hi : i ≤ k) :
    (weights.getD i 0 : ℚ) = d * hahnWeight n w k i := by
  have he := List.all_eq_true.mp h i (List.mem_range.mpr (by omega))
  simp only [beq_iff_eq] at he
  have he' : (weights.getD i 0 : ℚ) * (Nat.fast_choose w i : ℚ) =
      (-1 : ℚ)^i * Nat.fast_choose (n + i - (w + k)) i * d := by
    exact_mod_cast he
  have hpos : (Nat.fast_choose w i : ℚ) ≠ 0 := by
    rw [← Nat.choose_eq_fast_choose]
    exact_mod_cast (Nat.choose_pos (by omega : i ≤ w)).ne'
  rw [hahnWeight, Nat.choose_eq_fast_choose, ← mul_div_assoc]
  apply (eq_div_iff hpos).mpr
  rw [he']
  ring

theorem cast_kernel (n w k t d : ℕ) (weights : List ℤ)
    (hw : ∀ i ≤ k, (weights.getD i 0 : ℚ) = d * hahnWeight n w k i) :
    (kernel n w k t weights : ℚ) = (d : ℚ)^2 * hahnKernel n w k t := by
  unfold kernel hahnKernel
  simp only [sum_eq, Int.cast_sum, Int.cast_mul]
  rw [mul_sum]
  apply sum_congr rfl
  intro i hi
  have hi' : i ≤ k := by simpa using mem_range.mp hi
  rw [hw i hi']
  simp only [mul_sum]
  apply sum_congr rfl
  intro a ha
  have ha' : a ≤ i := by simpa using mem_range.mp ha
  split_ifs with hz
  · have hz' : (t.choose a * (w - t).choose (i - a) : ℚ) = 0 := by
      exact_mod_cast (show t.choose a * (w - t).choose (i - a) = 0 by
        simpa only [Nat.choose_eq_fast_choose] using hz)
    simp [hz']
  · simp only [Int.cast_mul, Int.cast_natCast, Int.cast_sum, mul_sum]
    apply sum_congr rfl
    intro c hc
    have hc' : c ≤ k - i := by simpa using mem_range.mp hc
    rw [hw (a + c) (by omega)]
    simp only [Nat.cast_mul, Nat.choose_eq_fast_choose]
    ring

theorem cast_eval (p : List ℤ) (x : ℤ) :
    (eval p x : ℚ) = (Identity.ofList p).eval (x : ℚ) := by
  induction p with
  | nil => simp [eval, Identity.ofList]
  | cons a p ih => simp [eval, Identity.ofList, ih]

theorem kernel_eq_eval (n w k : ℕ) (weights : List ℤ) (denom : ℕ)
    (coeffs : List ℤ) (polyDenom : ℕ)
    (hk : k ≤ w) (hn : w + k ≤ n) (hd : 0 < denom) (hp : 0 < polyDenom)
    (hlen : coeffs.length ≤ k + 1)
    (hw : weightsCheck n w k denom weights = true)
    (hc : check n w k weights denom coeffs polyDenom = true) (x : ℚ) :
    Fast.kernel n w k x = Fast.eval (coeffs.map fun a : ℤ => (a : ℚ) / polyDenom) x := by
  apply Identity.kernel_eq_of_values n w k coeffs polyDenom hlen hk
  intro t ht
  have he := List.all_eq_true.mp hc t (List.mem_range.mpr (by omega))
  simp only [beq_iff_eq] at he
  have he' : (kernel n w k (w - t) weights : ℚ) * polyDenom =
      (eval coeffs (w - t : ℕ) : ℚ) * (denom : ℚ)^2 := by exact_mod_cast he
  rw [cast_kernel n w k (w - t) denom weights (weightsCheck_sound n w k denom weights hk hw),
    cast_eval] at he'
  rw [Fast.kernel_nat n w k (w - t) (by omega) (by omega)]
  have hd' : (denom : ℚ)^2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hd.ne')
  have hp' : (polyDenom : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  apply (eq_div_iff hp').mpr
  apply (mul_left_cancel₀ hd')
  convert he' using 1 <;> push_cast <;> ring

end CodingTheory.HahnDelsarte.Fast.Integral
