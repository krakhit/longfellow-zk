import SumcheckV2.Layer
import SumcheckV1.Grinding

/-!
# V2 challenge-tape bounds

All messages and incoming states depend only on earlier challenges, by the types
of the strategies. The current challenge is drawn after its message is fixed.
We reuse only the protocol-independent counting in `SumcheckV1.Grinding`.
These are finite challenge-tape bounds, not a claim about a concrete hash function
or a proof of the complete commitment/Fiat--Shamir composition.
-/

namespace SumcheckV2

open Classical
open SumcheckV1 (Prefix extract_prefix)

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

inductive ChallengeKind where
  | round
  | combine
  deriving DecidableEq

def ChallengeKind.budget : ChallengeKind → ℕ
  | .round => 2
  | .combine => 1

structure RoundData (F : Type) [Field F] where
  truth : Polynomial F
  message : RoundPoly F
  claim : F

structure CombineData (F : Type) where
  trueA : F
  trueB : F
  claimA : F
  claimB : F

def ChallengeData (F : Type) [Field F] : ChallengeKind → Type
  | .round => RoundData F
  | .combine => CombineData F

def ChallengeData.Valid {kind : ChallengeKind} : ChallengeData F kind → Prop :=
  match kind with
  | .round => fun data => data.truth.natDegree ≤ 2
  | .combine => fun _ => True

def ChallengeData.Bad {kind : ChallengeKind} : ChallengeData F kind → F → Prop :=
  match kind with
  | .round => fun data z => BadRoundEvent data.truth data.message data.claim z
  | .combine => fun data alpha =>
      BadCombineEvent data.trueA data.trueB data.claimA data.claimB alpha

theorem challenge_bad_card_le {kind : ChallengeKind} (data : ChallengeData F kind)
    (hvalid : data.Valid) :
    (Finset.univ.filter fun z => data.Bad z).card ≤ kind.budget := by
  cases kind with
  | round => exact bad_round_roots data.truth data.message data.claim hvalid
  | combine => exact bad_combine_roots data.trueA data.trueB data.claimA data.claimB

/-- The protocol fixes the order of round challenges and final-claim combinations.
The strategy can adapt to the entire earlier prefix, including earlier layers. -/
abbrev LayerStrategy (F : Type) [Field F] {n : ℕ} (kinds : Fin n → ChallengeKind) :=
  ∀ i : Fin n, Prefix F i.val → ChallengeData F (kinds i)

/-- A round-only tape uses the same data and bad event as a mixed layer tape. -/
abbrev RoundStrategy (F : Type) [Field F] (n : ℕ) :=
  LayerStrategy F (fun _ : Fin n => .round)

def layer_bad_event {n : ℕ} {kinds : Fin n → ChallengeKind}
    (strategy : LayerStrategy F kinds) (cs : Fin n → F) : Prop :=
  ∃ i, (strategy i (extract_prefix cs i)).Bad (cs i)

/-- Each sumcheck challenge costs two roots and each final-claim combination one.
For `R` round slots and `L` combination slots, the numerator is `2R + L`. -/
theorem layer_tape_card_le {n : ℕ} (kinds : Fin n → ChallengeKind)
    (strategy : LayerStrategy F kinds) (hvalid : ∀ i pref, (strategy i pref).Valid) :
    (Finset.univ.filter fun cs : Fin n → F => layer_bad_event strategy cs).card ≤
      (∑ i, (kinds i).budget) * Fintype.card F ^ (n - 1) := by
  simpa only [layer_bad_event] using SumcheckV1.tape_bad_card_le (fun i => (kinds i).budget)
    (fun i pref z => (strategy i pref).Bad z)
    (fun i pref => challenge_bad_card_le (strategy i pref) (hvalid i pref))

/-- One round slot contributes at most two roots for each earlier prefix. -/
theorem combinatorial_fs_level {n : ℕ} (strategy : RoundStrategy F n)
    (hvalid : ∀ i pref, ChallengeData.Valid (strategy i pref)) (i : Fin n) :
    (Finset.univ.filter fun cs : Fin n → F =>
      ChallengeData.Bad (strategy i (extract_prefix cs i)) (cs i)).card ≤
        2 * Fintype.card F ^ (n - 1) :=
  SumcheckV1.slot_bad_card_le i 2
    (fun pref z => ChallengeData.Bad (strategy i pref) z)
    (fun pref => challenge_bad_card_le (strategy i pref) (hvalid i pref))

/-- The round-only specialization: `2n / |F|` as a count of bad tapes, including `n = 0`. -/
theorem combinatorial_fiat_shamir {n : ℕ} (strategy : RoundStrategy F n)
    (hvalid : ∀ i pref, ChallengeData.Valid (strategy i pref)) :
    (Finset.univ.filter fun cs : Fin n → F => layer_bad_event strategy cs).card ≤
      n * 2 * Fintype.card F ^ (n - 1) := by
  simpa [ChallengeKind.budget] using layer_tape_card_le (fun _ => .round) strategy hvalid

end SumcheckV2
