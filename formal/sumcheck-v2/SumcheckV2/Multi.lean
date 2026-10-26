import SumcheckV2.Round

/-!
# V2 round chains

The claimed state follows the transmitted coefficients. The true state follows
the true round polynomials. Empty chains are included: a scalar layer has zero
rounds, and its incoming claim is checked directly by the terminal product.
-/

namespace SumcheckV2

open Polynomial

variable {F : Type} [Field F]

def verify_multi_round (claim : F) : List (RoundPoly F) → List F → Option F
  | [], [] => some claim
  | p :: ps, z :: zs => verify_multi_round (check_round claim p z) ps zs
  | _, _ => none

/-- Successive true projective sums equal the preceding evaluation. -/
def Consistent (truth : F) : List (Polynomial F) → List F → Prop
  | [], [] => True
  | P :: Ps, z :: zs => projectiveSum P = truth ∧ Consistent (P.eval z) Ps zs
  | _, _ => False

def true_final (truth : F) : List (Polynomial F) → List F → Option F
  | [], [] => some truth
  | P :: Ps, z :: zs => true_final (P.eval z) Ps zs
  | _, _ => none

/-- The bad event uses the actual incoming claimed state at each round. -/
def multi_round_bad_event (claim : F) :
    List (Polynomial F) → List (RoundPoly F) → List F → Prop
  | P :: Ps, p :: ps, z :: zs =>
      BadRoundEvent P p claim z ∨
        multi_round_bad_event (check_round claim p z) Ps ps zs
  | _, _, _ => False

/-- An accepted false claim reaching the correct terminal value has a bad round. -/
theorem sumcheck_multi_reduction
    (Ps : List (Polynomial F)) (messages : List (RoundPoly F)) (challenges : List F)
    (claim truth final : F)
    (hcons : Consistent truth Ps challenges)
    (hverify : verify_multi_round claim messages challenges = some final)
    (hfinal : true_final truth Ps challenges = some final)
    (hfalse : claim ≠ truth) : multi_round_bad_event claim Ps messages challenges := by
  induction messages generalizing Ps challenges claim truth with
  | nil =>
      cases challenges with
      | nil =>
          cases Ps with
          | nil => simp_all [verify_multi_round, true_final]
          | cons P Ps => simp [Consistent] at hcons
      | cons z zs => simp [verify_multi_round] at hverify
  | cons p ps ih =>
      cases challenges with
      | nil => simp [verify_multi_round] at hverify
      | cons z zs =>
          cases Ps with
          | nil => simp [Consistent] at hcons
          | cons P Ps =>
              obtain ⟨hstart, hrest⟩ := hcons
              have hwrong : claim ≠ projectiveSum P := by simpa [hstart] using hfalse
              rcases sumcheck_step_reduction P p claim z hwrong with hnext | hbad
              · exact Or.inr (ih Ps zs (check_round claim p z) (P.eval z)
                  hrest hverify hfinal hnext)
              · exact Or.inl hbad

/-- Honest degree-two messages preserve the true chain, including zero rounds. -/
theorem sumcheck_multi_completeness (Ps : List (Polynomial F)) (challenges : List F)
    (truth : F) (hcons : Consistent truth Ps challenges)
    (hdeg : ∀ P ∈ Ps, P.natDegree ≤ 2) :
    verify_multi_round truth (Ps.map RoundPoly.ofPoly) challenges =
      true_final truth Ps challenges := by
  induction Ps generalizing challenges truth with
  | nil =>
      cases challenges <;> simp_all [Consistent, verify_multi_round, true_final]
  | cons P Ps ih =>
      cases challenges with
      | nil => simp [Consistent] at hcons
      | cons z zs =>
          obtain ⟨hstart, hrest⟩ := hcons
          simp only [List.map_cons, verify_multi_round, true_final]
          rw [← hstart, sumcheck_step_completeness P (hdeg P (by simp))]
          exact ih zs (P.eval z) hrest (fun Q hQ => hdeg Q (by simp [hQ]))

@[simp] theorem verify_multi_round_nil (claim : F) :
    verify_multi_round claim [] [] = some claim := rfl

end SumcheckV2
