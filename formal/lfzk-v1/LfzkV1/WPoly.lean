import SumcheckV1

/-!
# Longfellow's round-polynomial format

`../sumcheck-v1/` is the generic affine-endpoint development: round polynomials of any degree `d`, the round
reduction and its completeness converse, and the Fiat–Shamir counting bound.  This file is the
*specialisation* — everything Longfellow-specific about how it transmits a round polynomial, and
nothing else.

The specialisation is `d = 2`: Longfellow's `WPoly = Poly<3, Field>` is three evaluations, at
`0`, `1`, and `Field::poly_evaluation_point(2)`.  Its `CPoly = Poly<4, Field>` — degree `3`, used
by the copy rounds of the **non-ZK** verifier — is `SumcheckV1.RoundPoly F 3` and is not used here,
because the ZK path asserts `logc == 0` (`zk_common.h:L72`). The copy-round counting bound is
`SumcheckV1.combinatorial_fiat_shamir` specialized to `d = 3` and `deg = 3`.

Everything else Longfellow — the quad format and its gate table, the layer polynomial, the
`ConstraintBuilder` recursion, the pad layout, `ArithmetizedCircuit` / `LayeredCircuit` — stays in
`lfzk-v1/`, because none of it is about sumcheck.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SumcheckV1

/-- **Longfellow's `WPoly` format.**  Three evaluation points, hence degree `2`.

The third point is left abstract by `SumcheckV1.Interp`, which is what this needs: it is `2` over a
prime field but the generator `X` over `GF(2)[X]/(Q(X))`, where `2 = 0`. -/
abbrev SumcheckV1Interp (F : Type) [Field F] := SumcheckV1.Interp F 2

namespace SumcheckV1.RoundPoly

/-- The third transmitted evaluation, `tp[2]`.  `eval0` and `eval1` are generic — the sum check
reads them at every degree — but a *third* one is specific to `WPoly`. -/
abbrev eval2 {F : Type} [Field F] (p : RoundPoly F 2) : F := p.evals 2

end SumcheckV1.RoundPoly

/-- `Field::poly_evaluation_point(2)`: the third node of a `WPoly`. -/
abbrev pt2 {F : Type} [Field F] [SumcheckV1Interp F] : F :=
  SumcheckV1.Interp.pts (F := F) (d := 2) 2

namespace SumcheckV1Interp

variable {F : Type} [Field F] [SumcheckV1Interp F]

/-- The third node is distinct from `0`.  Derived from injectivity of the node vector, where it
used to be a field of the class. -/
lemma pt2_ne_zero : (pt2 : F) ≠ 0 := by
  rw [← SumcheckV1.Interp.pts_zero (F := F) (d := 2)]
  exact fun h => absurd (SumcheckV1.Interp.pts_inj h) (by decide)

/-- The third node is distinct from `1`. -/
lemma pt2_ne_one : (pt2 : F) ≠ 1 := by
  rw [← SumcheckV1.Interp.pts_one (F := F) (d := 2)]
  exact fun h => absurd (SumcheckV1.Interp.pts_inj h) (by decide)

end SumcheckV1Interp

namespace SumcheckV1.RoundPoly

/--
**Three-point agreement, in `WPoly` form.**

`SumcheckV1.RoundPoly.eval_lagrange_eq_of_agree` asks for agreement at every node as one `∀ i`;
at `d = 2` that is three named hypotheses, which is how the Longfellow proofs supply it.
-/
lemma wpoly_agree {F : Type} [Field F] [SumcheckV1Interp F] (p : RoundPoly F 2)
    (P : Polynomial F) (hdeg : P.natDegree ≤ 2)
    (h0 : p.eval0 = P.eval 0) (h1 : p.eval1 = P.eval 1) (h2 : p.eval2 = P.eval (pt2 : F))
    (r : F) : p.eval_lagrange r = P.eval r := by
  refine p.eval_lagrange_eq_of_agree P hdeg (fun i => ?_) r
  fin_cases i
  · simpa [SumcheckV1.Interp.pts_zero] using h0
  · simpa [SumcheckV1.Interp.pts_one] using h1
  · exact h2

end SumcheckV1.RoundPoly

namespace SumcheckV1.RoundPoly

variable {F : Type} [Field F] [SumcheckV1Interp F]

omit [Field F] [SumcheckV1Interp F] in
@[simp] lemma mk_eval0 (a b c : F) : (⟨![a, b, c]⟩ : RoundPoly F 2).eval0 = a := rfl
omit [Field F] [SumcheckV1Interp F] in
@[simp] lemma mk_eval1 (a b c : F) : (⟨![a, b, c]⟩ : RoundPoly F 2).eval1 = b := rfl
omit [SumcheckV1Interp F] in
@[simp] lemma mk_eval2 (a b c : F) : (⟨![a, b, c]⟩ : RoundPoly F 2).eval2 = c := rfl

/--
**`eval_lagrange` at `d = 2`, in closed form.**

The generic definition is a sum of `d + 1` Lagrange terms; at `d = 2` it is the three-term
expression `Poly<3, Field>::eval_lagrange` computes (`algebra/poly.h`).  This is the form the
`ConstraintBuilder` proofs are written against — `lag_coeffs` is literally these three
coefficients.
-/
lemma eval_lagrange_two (p : RoundPoly F 2) (r : F) :
    p.eval_lagrange r
      = p.eval0 * ((r - 1) * (r - (pt2 : F))) * (pt2 : F)⁻¹
      + p.eval1 * (r * (r - (pt2 : F))) * (1 - (pt2 : F))⁻¹
      + p.eval2 * (r * (r - 1)) * ((pt2 : F) * ((pt2 : F) - 1))⁻¹ := by
  have h0 : SumcheckV1.Interp.pts (F := F) (d := 2) 0 = 0 := SumcheckV1.Interp.pts_zero
  have h1 : SumcheckV1.Interp.pts (F := F) (d := 2) 1 = 1 := SumcheckV1.Interp.pts_one
  have hz : SumcheckV1.Interp.pts (F := F) (d := 2) 2 ≠ 0 := SumcheckV1Interp.pt2_ne_zero
  have ho : (1 : F) - SumcheckV1.Interp.pts (F := F) (d := 2) 2 ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm SumcheckV1Interp.pt2_ne_one)
  have ho' : SumcheckV1.Interp.pts (F := F) (d := 2) 2 - 1 ≠ 0 :=
    sub_ne_zero.mpr SumcheckV1Interp.pt2_ne_one
  have hsum : ∀ f : Fin 3 → F, ∑ i, f i = f 0 + f 1 + f 2 := fun f => by
    simp [Fin.sum_univ_three]
  rw [eval_lagrange, hsum]
  rw [show (Finset.univ.erase (0 : Fin 3)) = {1, 2} from by decide,
      show (Finset.univ.erase (1 : Fin 3)) = {0, 2} from by decide,
      show (Finset.univ.erase (2 : Fin 3)) = {0, 1} from by decide,
      Finset.prod_pair (by decide : (1 : Fin 3) ≠ 2),
      Finset.prod_pair (by decide : (0 : Fin 3) ≠ 2),
      Finset.prod_pair (by decide : (0 : Fin 3) ≠ 1), h0, h1]
  field_simp [hz, ho, ho']
  ring

end SumcheckV1.RoundPoly
