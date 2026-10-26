import polygero.FiatShamir.ExtractionBudgets
import Bcs.QueryRoleCompiler

/-! Nonrecursive Polygero soundness against adaptive classical hash-query
programs. The two query roles bind the commitment context and the complete
response. The context is independent of the two answers being counted.
The concrete verifier and both response polynomials enter the counting proof.
-/

noncomputable section
namespace RecursivePolygero.NonrecursiveFS
open Polynomial Finset Codes Local ProfileAnalysis
open Bcs.TotalOracle Merkle.RandomOracle
open scoped Classical
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq F] in
theorem rank_high_le_error (I : Instance F) (p : HahnSystemCertificate I)
    (hsmall : p.rankError ≤ 1/(Nat.card F : ℚ)) :
    p.rankError + highBudget I p ≤ p.error := by
  have h := mul_nonneg p.threshold_nonneg (sub_nonneg.mpr hsmall)
  have hq : (Nat.card F : ℚ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := F)).ne'
  calc
    _ ≤ p.rankError + highBudget I p + p.threshold * (1/(Nat.card F : ℚ)-p.rankError) :=
      le_add_of_nonneg_right h
    _ = p.error := by
      unfold highBudget HahnSystemCertificate.error profile
      field_simp
      ring

/-- Adaptive Fiat–Shamir acceptance without a decoded witness. The statement
may be satisfiable and may depend on all oracle coordinates outside the two
backend points. This is the extraction term needed by a composed frontend. -/
theorem extraction_failure_le
    (I : Instance F) (p : HahnSystemCertificate I)
    (hsmall : p.rankError ≤ 1/(Nat.card F : ℚ))
    {C Pt Out Parent State : Type}
    [Fintype C] [Nonempty C] [Fintype Pt] [DecidableEq Pt] [Fintype Parent]
    {N : ℕ} (tree : Tree Pt C Out N) (selected : Out → Parent × I.layer.Payload)
    (parent : Parent → Pt) (child : Parent → I.layer.Payload → Pt)
    (hparent : Function.Injective parent)
    (hchild : Function.Injective (fun i : Parent × I.layer.Payload => child i.1 i.2))
    (hdisjoint : ∀ j j' payload, parent j ≠ child j' payload)
    (state : Parent → (Pt → C) → State)
    (hstateOff : ∀ j payload H H',
      (∀ z, z ≠ parent j → z ≠ child j payload → H z = H' z) → state j H = state j H')
    (statement : State → Parent → I.layer.Statement)
    (oracle : State → Parent → I.layer.Oracle)
    [DecidableEq I.layer.Coin] [DecidableEq I.layer.Query]
    (decodeCoin : C → I.layer.Coin) (decodeQuery : C → I.layer.Query)
    (kCoin kQuery : ℕ)
    (hcoin : ∀ coin, (univ.filter fun a : C => decodeCoin a = coin).card ≤ kCoin)
    (hquery : ∀ Q, (univ.filter fun b : C => decodeQuery b = Q).card ≤ kQuery)
    (hkCoin : kCoin*Fintype.card I.layer.Coin ≤ Fintype.card C)
    (hkQuery : kQuery*Fintype.card I.layer.Query ≤ Fintype.card C) :
    let failure := fun H : Pt → C =>
      let i := selected (tree.run H).1
      let σ := statement (state i.1 H) i.1
      let W := oracle (state i.1 H) i.1
      let coin := decodeCoin (H (parent i.1))
      I.layer.verify σ W coin i.2 (decodeQuery (H (child i.1 i.2))) ∧
        scanRecoverAt I σ W coin i.2 = none
    ((univ.filter failure).card : ℚ)/(Fintype.card C : ℚ)^Fintype.card Pt ≤
      (N+1 : ℕ)*p.error := by
  convert! tree_query_role_final_ratio_le tree selected parent child hparent hchild hdisjoint
    state hstateOff
    (fun s j payload a b => I.layer.verify (statement s j) (oracle s j)
      (decodeCoin a) payload (decodeQuery b) ∧
        scanRecoverAt I (statement s j) (oracle s j) (decodeCoin a) payload = none)
    (fun s j a => rankBad I (oracle s j) (decodeCoin a))
    (fun s j payload a => p.error < fraction I (statement s j) (oracle s j) (decodeCoin a) payload)
    p.error p.rankError (highBudget I p) p.error_nonneg (rank_high_le_error I p hsmall)
    ?_ ?_ ?_ ?_ using 1
  · simp only
  · intro s j payload
    convert! failure_fixed_response_raw_le I p decodeCoin decodeQuery kCoin kQuery hcoin hquery
      hkCoin hkQuery (statement s j) (oracle s j) payload using 1
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro b _
    split_ifs <;> rfl
  · intro s j
    exact rank_raw_le I p decodeCoin kCoin hcoin hkCoin (oracle s j)
  · intro s j payload a
    convert! failure_low_raw_le I p decodeQuery kQuery hquery hkQuery
      (statement s j) (oracle s j) (decodeCoin a) payload using 1
    apply sum_congr rfl
    intro b _
    split_ifs <;> rfl
  · intro s j
    convert! failure_high_raw_le I p decodeCoin decodeQuery kCoin kQuery hcoin hquery hkCoin hkQuery
      (statement s j) (oracle s j) using 1
    apply sum_congr rfl
    intro payload _
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro b _
    split_ifs <;> rfl

/-- The final verification event has probability at most `(N+1)*error`,
including proofs selected adaptively after the adversary's last oracle query.
The sampler hypotheses require balanced finite decoders; concrete hash and
sampler reductions can supply a separate error term. -/
theorem soundness_le
    (I : Instance F) (p : HahnSystemCertificate I)
    (hsmall : p.rankError ≤ 1/(Nat.card F : ℚ))
    {C Pt Out Parent State : Type}
    [Fintype C] [Nonempty C] [Fintype Pt] [DecidableEq Pt] [Fintype Parent]
    {N : ℕ} (tree : Tree Pt C Out N) (selected : Out → Parent × I.layer.Payload)
    (parent : Parent → Pt) (child : Parent → I.layer.Payload → Pt)
    (hparent : Function.Injective parent)
    (hchild : Function.Injective (fun i : Parent × I.layer.Payload => child i.1 i.2))
    (hdisjoint : ∀ j j' payload, parent j ≠ child j' payload)
    (state : Parent → (Pt → C) → State)
    (hstateOff : ∀ j payload H H',
      (∀ z, z ≠ parent j → z ≠ child j payload → H z = H' z) → state j H = state j H')
    (statement : State → Parent → I.layer.Statement)
    (oracle : State → Parent → I.layer.Oracle)
    (hfalse : ∀ s j w, ¬ I.layer.satisfies (statement s j) w)
    [DecidableEq I.layer.Coin] [DecidableEq I.layer.Query]
    (decodeCoin : C → I.layer.Coin) (decodeQuery : C → I.layer.Query)
    (kCoin kQuery : ℕ)
    (hcoin : ∀ coin, (univ.filter fun a : C => decodeCoin a = coin).card ≤ kCoin)
    (hquery : ∀ Q, (univ.filter fun b : C => decodeQuery b = Q).card ≤ kQuery)
    (hkCoin : kCoin*Fintype.card I.layer.Coin ≤ Fintype.card C)
    (hkQuery : kQuery*Fintype.card I.layer.Query ≤ Fintype.card C) :
    let accepts := fun H : Pt → C =>
      let i := selected (tree.run H).1
      I.layer.verify (statement (state i.1 H) i.1) (oracle (state i.1 H) i.1)
        (decodeCoin (H (parent i.1))) i.2 (decodeQuery (H (child i.1 i.2)))
    ((univ.filter accepts).card : ℚ)/(Fintype.card C : ℚ)^Fintype.card Pt ≤
      (N+1 : ℕ)*p.error := by
  apply tree_query_role_final_ratio_le tree selected parent child hparent hchild hdisjoint
    state hstateOff
    (fun s j payload a b => I.layer.verify (statement s j) (oracle s j)
      (decodeCoin a) payload (decodeQuery b))
    (fun s j a => rankBad I (oracle s j) (decodeCoin a))
    (fun s j payload a => p.error < fraction I (statement s j) (oracle s j) (decodeCoin a) payload)
    p.error p.rankError (highBudget I p) p.error_nonneg (rank_high_le_error I p hsmall)
  · intro s j payload
    exact fixed_response_raw_le I p decodeCoin decodeQuery kCoin kQuery hcoin hquery
      hkCoin hkQuery (statement s j) (oracle s j) (hfalse s j) payload
  · intro s j
    exact rank_raw_le I p decodeCoin kCoin hcoin hkCoin (oracle s j)
  · intro s j payload a
    convert! low_raw_le I p decodeQuery kQuery hquery hkQuery
      (statement s j) (oracle s j) (decodeCoin a) payload using 1
    apply sum_congr rfl
    intro b _
    split_ifs <;> rfl
  · intro s j
    convert! high_raw_le I p decodeCoin decodeQuery kCoin kQuery hcoin hquery hkCoin hkQuery
      (statement s j) (oracle s j) (hfalse s j) using 1
    apply sum_congr rfl
    intro payload _
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro b _
    split_ifs <;> rfl

end RecursivePolygero.NonrecursiveFS
