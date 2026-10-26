import LfzkV2.Events
import Bcs.TotalOracle

/-!
# V2 Fiat--Shamir challenge grinding

This uses a total random oracle on finite, domain-separated message-prefix
points. An adversary may query points in any order and choose its final proof
adaptively. It is not restricted to an honest sequential challenge tape.

`Setup` states the transcript/commitment boundary explicitly. Contexts must be
fixed off the point being counted. `Covers` identifies the concrete algebraic
tests of a reconstructed circuit execution with those prefix-local tests; it
does not assume a soundness bound or an acceptance-to-bad-event implication.
-/

namespace LfzkV2.FiatShamir

open SumcheckV2 Classical Finset Bcs.TotalOracle Merkle.RandomOracle
attribute [local instance 10000] Classical.propDecidable

variable {F Q Out Key Context Candidate : Type} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Candidate] [DecidableEq Q] {N L : ℕ}

structure Setup (F : Type) [Field F] [Fintype F]
    (Q Out Key Context Candidate : Type) [DecidableEq Q] (N L : ℕ) where
  adversary : Tree Q F Out N
  hashInput : Out → ℕ → Q
  points : PrefixPoints Q
  key : Q → Key
  context : (Q → F) → Key → Context
  context_off : ∀ (H H' : Q → F) (x : Q), AgreeOff x H H' →
    context H' (key x) = context H (key x)
  test : Context → (x : Q) → (Fin (points.slot x) → F) → Candidate → ChallengeTest F
  valid : ∀ ctx x pref candidate, (test ctx x pref candidate).Valid
  budget : Q → ℕ
  test_budget : ∀ ctx x pref candidate, (test ctx x pref candidate).budget ≤ budget x

namespace Setup

variable (S : Setup F Q Out Key Context Candidate N L)

theorem bad_bound (ctx : Context) (x : Q) (pref : Fin (S.points.slot x) → F) :
    (univ.filter fun z => ∃ candidate, (S.test ctx x pref candidate).Bad z).card ≤
      Fintype.card Candidate * S.budget x := by
  have heq : (univ.filter fun z => ∃ candidate, (S.test ctx x pref candidate).Bad z) =
      univ.biUnion (fun candidate => univ.filter (S.test ctx x pref candidate).Bad) := by
    ext z
    simp
  rw [heq]
  calc
    _ ≤ ∑ candidate, (univ.filter (S.test ctx x pref candidate).Bad).card := card_biUnion_le
    _ ≤ ∑ _ : Candidate, S.budget x := sum_le_sum fun candidate _ =>
      ((S.test ctx x pref candidate).card_bad_le (S.valid ctx x pref candidate)).trans
        (S.test_budget ctx x pref candidate)
    _ = _ := by simp

noncomputable def grinding : CtxGrinding F Q Out Key Context N L where
  adversary := S.adversary
  hashInput := S.hashInput
  pts := S.points
  key := S.key
  ctxAt := S.context
  ctxAt_off := S.context_off
  Bad ctx x pref z := ∃ candidate, (S.test ctx x pref candidate).Bad z
  beta x := Fintype.card Candidate * S.budget x
  bad_bound := S.bad_bound

/-- Every numerical test is assigned to its actual verifier oracle point.
The data equality includes the incoming claim and the unmasked coefficients. -/
def Covers (H : Q → F) (candidate : Candidate) (tests : Tests F) : Prop :=
  ∀ test ∈ tests, ∃ i : Fin L,
    let x := S.hashInput (S.adversary.run H).1 i.val
    test.1 = S.test (S.context H (S.key x)) x (S.points.chal H x) candidate ∧
      test.2 = H x

theorem bad_of_tests (H : Q → F) (candidate : Candidate) (tests : Tests F)
    (hcover : S.Covers H candidate tests) (hbad : tests.Bad) : S.grinding.RoundBad H := by
  obtain ⟨test, hmem, htest⟩ := hbad
  obtain ⟨i, hdata, hcoin⟩ := hcover test hmem
  refine ⟨i, candidate, ?_⟩
  change (S.test (S.context H (S.key (S.hashInput (S.adversary.run H).1 i.val)))
    (S.hashInput (S.adversary.run H).1 i.val)
    (S.points.chal H (S.hashInput (S.adversary.run H).1 i.val)) candidate).Bad
      (H (S.hashInput (S.adversary.run H).1 i.val))
  rwa [← hdata, ← hcoin]

/-- Query-aware finite random-oracle bound, including adaptive proof selection.
One candidate-list factor covers all tests, rather than one factor per layer. -/
theorem soundness_le [Fintype Q] (maxBudget : ℕ) (hmax : ∀ x, S.budget x ≤ maxBudget)
    (slotBudget : Fin L → ℕ)
    (hslot : ∀ out i, S.budget (S.hashInput out i.val) ≤ slotBudget i)
    (event : (Q → F) → Prop)
    (htests : ∀ H, event H → ∃ candidate tests, S.Covers H candidate tests ∧ tests.Bad) :
    ((univ.filter event).card : ℚ) / (Fintype.card F : ℚ) ^ Fintype.card Q ≤
      (Fintype.card Candidate : ℚ) * (N * maxBudget + ∑ i, slotBudget i) / Fintype.card F := by
  have h := S.grinding.ratio_le (Fintype.card Candidate * maxBudget)
    (fun x => Nat.mul_le_mul_left _ (hmax x))
    (fun i => Fintype.card Candidate * slotBudget i)
    (fun out i => Nat.mul_le_mul_left _ (hslot out i)) event (fun H hE => by
      obtain ⟨candidate, tests, hcover, hbad⟩ := htests H hE
      exact S.bad_of_tests H candidate tests hcover hbad)
  rw [← Finset.mul_sum] at h
  convert h using 1
  push_cast
  ring

end Setup

namespace Setup

/-- Restrict the candidate family while retaining the same transcript, contexts,
and local root bounds. In particular, a fixed witness needs only one candidate. -/
def restrictCandidates {Candidate' : Type}
    (S : Setup F Q Out Key Context Candidate N L) (f : Candidate' → Candidate) :
    Setup F Q Out Key Context Candidate' N L where
  adversary := S.adversary
  hashInput := S.hashInput
  points := S.points
  key := S.key
  context := S.context
  context_off := S.context_off
  test ctx x pref candidate := S.test ctx x pref (f candidate)
  valid ctx x pref candidate := S.valid ctx x pref (f candidate)
  budget := S.budget
  test_budget ctx x pref candidate := S.test_budget ctx x pref (f candidate)

omit [Fintype Candidate] in
/-- The adaptive oracle bound for one fixed candidate. Its cost is independent
of the cardinality of the ambient family of witnesses. -/
theorem fixed_candidate_soundness_le [Fintype Q]
    (S : Setup F Q Out Key Context Candidate N L) (candidate : Candidate)
    (maxBudget : ℕ) (hmax : ∀ x, S.budget x ≤ maxBudget)
    (slotBudget : Fin L → ℕ)
    (hslot : ∀ out i, S.budget (S.hashInput out i.val) ≤ slotBudget i)
    (event : (Q → F) → Prop)
    (htests : ∀ H, event H → ∃ tests, S.Covers H candidate tests ∧ tests.Bad) :
    ((univ.filter event).card : ℚ) / (Fintype.card F : ℚ) ^ Fintype.card Q ≤
      (N * maxBudget + ∑ i, slotBudget i) / Fintype.card F := by
  have h := (S.restrictCandidates (fun _ : Unit => candidate)).soundness_le
    maxBudget hmax slotBudget hslot event (by
      intro H hH
      obtain ⟨tests, hcover, hbad⟩ := htests H hH
      exact ⟨(), tests, hcover, hbad⟩)
  simpa using h

end Setup

end LfzkV2.FiatShamir
