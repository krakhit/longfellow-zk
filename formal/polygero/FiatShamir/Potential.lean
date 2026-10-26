import polygero.FiatShamir.ExtractionBudgets
import polygero.Local.CommittedCandidates
import LigeroFamily.Soundness.PotentialProfile
import LfzkV1.ZkPotentialBalance

/-! Polygero's local interface to V1's graded terminal accounting. The
potential is evaluated at the maximum agreement of an extraction-failing
complete response, before any response is selected. The final opening pays
the same residual query cost as V1. -/

namespace RecursivePolygero.NonrecursiveFS

open Finset LigeroFamily Local.Polygero ProfileAnalysis
open scoped Classical

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

noncomputable def failureCoordinates (I : Instance F) (σ : I.layer.Statement) (W : I.layer.Oracle)
    (coin : I.layer.Coin) (response : I.layer.Payload) : Finset (Fin I.n) :=
  if scanRecoverAt I σ W coin response = none ∧ globalCheck I.domain I.layout σ coin.1 response then
    good I σ W coin response else ∅

noncomputable def maxFailureAgreement (I : Instance F) (σ : I.layer.Statement) (W : I.layer.Oracle)
    (coin : I.layer.Coin) : ℕ :=
  univ.sup fun response : I.layer.Payload => (failureCoordinates I σ W coin response).card

theorem maxFailureAgreement_le (I : Instance F) (σ : I.layer.Statement) (W : I.layer.Oracle)
    (coin : I.layer.Coin) : maxFailureAgreement I σ W coin ≤ I.n := by
  apply Finset.sup_le
  intro response _
  exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)

theorem le_maxFailureAgreement_iff (I : Instance F) (σ : I.layer.Statement) (W : I.layer.Oracle)
    (coin : I.layer.Coin) {a : ℕ} (ha : 0 < a) :
    a ≤ maxFailureAgreement I σ W coin ↔ ∃ response : I.layer.Payload,
      scanRecoverAt I σ W coin response = none ∧ globalCheck I.domain I.layout σ coin.1 response ∧
        a ≤ (good I σ W coin response).card := by
  constructor
  · intro hmax
    have hex : ∃ response : I.layer.Payload, a ≤ (failureCoordinates I σ W coin response).card := by
      by_contra! hn
      have hsmall : maxFailureAgreement I σ W coin ≤ a-1 := by
        apply Finset.sup_le
        intro response _
        have := hn response
        omega
      omega
    obtain ⟨response,hr⟩ := hex
    unfold failureCoordinates at hr
    split_ifs at hr with h
    · exact ⟨response,h.1,h.2,hr⟩
    · simp only [card_empty] at hr
      omega
  · rintro ⟨response,hnone,hglobal,hsize⟩
    have hs : (failureCoordinates I σ W coin response).card ≤ maxFailureAgreement I σ W coin :=
      Finset.le_sup (f := fun response : I.layer.Payload =>
        (failureCoordinates I σ W coin response).card) (mem_univ response)
    have hsize' : a ≤ (failureCoordinates I σ W coin response).card := by
      rw [failureCoordinates, if_pos (And.intro hnone hglobal)]
      exact hsize
    exact hsize'.trans hs

/-- Outside the rank event, the maximum of all failing responses is covered
by fixed system exceptions, using the existing Polygero recovery theorem. -/
theorem maxFailureAgreement_system_exception (I : Instance F) (p : ProfileParameters I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin) {a : ℕ}
    (hlarge : p.largeSize ≤ a) (ha : a ≤ maxFailureAgreement I σ W coin)
    (hrank : ¬ rankBad I W coin) :
    ∃ d : systems I.domain I.primary_le W,
      a ≤ Local.ReducedSystems.capacity (code I) (words I W) W.proximityMask d.1 ∧
        coin ∈ systemExceptions p.positive_degree I.layout σ d := by
  have hpos : 0 < a := by
    have hcore := (le_max_left _ _).trans hlarge
    change I.r+I.w+I.s+I.s+1 ≤ a at hcore
    omega
  obtain ⟨response,hnone,hglobal,hsize⟩ := (le_maxFailureAgreement_iff I σ W coin hpos).mp ha
  have hg := hlarge.trans hsize
  obtain ⟨d,hcapacity,hout⟩ := large_response I p.positive_degree σ W coin response hglobal hrank
    ((le_max_left _ _).trans hg) ((le_max_right _ _).trans hg)
  refine ⟨d,hsize.trans hcapacity,?_⟩
  rcases hout with he | ⟨hfull,he⟩
  · exact he
  · rw [hnone] at he
    cases he

noncomputable def capacityTail (I : Instance F) (W : I.layer.Oracle) (a : ℕ) :
    Finset (systems I.domain I.primary_le W) :=
  univ.filter fun d => a ≤ Local.ReducedSystems.capacity (code I) (words I W) W.proximityMask d.1

/-- The complete agreement tail supplies V1's curve compiler directly.
Each fixed reduced-system exception costs one field factor. -/
theorem maxFailureAgreement_tail_le (I : Instance F) (p : ProfileParameters I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) {a : ℕ} (hlarge : p.largeSize ≤ a) :
    mean (fun coin : I.layer.Coin => indicator (a ≤ maxFailureAgreement I σ W coin)) ≤
      p.rankError + (capacityTail I W a).card/(Nat.card F : ℚ) := by
  have hp (coin : I.layer.Coin) : indicator (a ≤ maxFailureAgreement I σ W coin) ≤
      indicator (rankBad I W coin) + ∑ d ∈ capacityTail I W a,
        indicator (coin ∈ systemExceptions p.positive_degree I.layout σ d) := by
    by_cases ha : a ≤ maxFailureAgreement I σ W coin
    · by_cases hb : rankBad I W coin
      · rw [show indicator (a ≤ maxFailureAgreement I σ W coin) = 1 by simp [indicator, ha],
          show indicator (rankBad I W coin) = 1 by simp [indicator, hb]]
        exact le_add_of_nonneg_right (sum_nonneg (fun _ _ => indicator_nonneg _))
      · obtain ⟨d,hd,he⟩ := maxFailureAgreement_system_exception I p σ W coin hlarge ha hb
        have hs := single_le_sum
          (fun d (_ : d ∈ capacityTail I W a) => indicator_nonneg
            (coin ∈ systemExceptions p.positive_degree I.layout σ d))
          (mem_filter.mpr ⟨mem_univ d,hd⟩)
        simpa only [indicator, if_pos ha, if_neg hb, if_pos he, zero_add] using hs
    · simp only [indicator, if_neg ha]
      exact add_nonneg (by split_ifs <;> norm_num)
        (sum_nonneg (fun _ _ => by split_ifs <;> norm_num))
  have hs : mean (fun coin : I.layer.Coin => ∑ d ∈ capacityTail I W a,
      indicator (coin ∈ systemExceptions p.positive_degree I.layout σ d)) ≤
        (capacityTail I W a).card/(Nat.card F : ℚ) := by
    rw [SystemException.mean_finset_sum]
    calc
      _ ≤ ∑ _d ∈ capacityTail I W a, 1/(Nat.card F : ℚ) :=
        sum_le_sum (fun d _ => systemExceptions_mean I p σ W d)
      _ = _ := by simp; ring
  have h := mean_mono hp
  rw [mean_add] at h
  exact h.trans (add_le_add (rank_bad_mean I p W) hs)

/-- The same checked family certificate used by V1 bounds every capacity
tail. The sets are the actual maximal associated sets of the fixed systems. -/
theorem capacityTail_card_le (I : Instance F) (p : ProfileParameters I)
    (W : I.layer.Oracle) (a L : ℕ) (hlow : p.overlapSize < a)
    (hbound : CodingTheory.UniformFamilyBound I.n a p.overlapSize L) :
    (capacityTail I W a).card ≤ L := by
  let E (d : systems I.domain I.primary_le W) : Finset (Fin I.n) :=
    Classical.choose (Local.ReducedSystems.capacity_witness
      (code I) (words I W) W.proximityMask d.1 d.2)
  have hspec (d : systems I.domain I.primary_le W) :
      E d ∈ Local.ReducedSystems.associatedSets (code I) (words I W) W.proximityMask d.1 ∧
      (E d).card = Local.ReducedSystems.capacity (code I) (words I W) W.proximityMask d.1 :=
    Classical.choose_spec (Local.ReducedSystems.capacity_witness
      (code I) (words I W) W.proximityMask d.1 d.2)
  apply DirectBinomial.active_card_le_of_uniformFamilyBound
    (capacityTail I W a) E a p.overlapSize L hlow
  · intro d hd
    rw [(hspec d).2]
    exact (mem_filter.mp hd).2
  · intro d _ e _ hne
    exact Local.ReducedSystems.associated_intersection (code I) (words I W) W.proximityMask
      p.positive_degree d.1 e.1 (E d) (E e) (hspec d).1 (hspec e).1
      (fun he => hne (Subtype.ext he))
  · exact hbound

theorem maxFailureAgreement_tail_le_of_uniformFamilyBound
    (I : Instance F) (p : ProfileParameters I) (σ : I.layer.Statement) (W : I.layer.Oracle)
    (a L : ℕ) (hlarge : p.largeSize ≤ a)
    (hbound : CodingTheory.UniformFamilyBound I.n a p.overlapSize L) :
    mean (fun coin : I.layer.Coin => indicator (a ≤ maxFailureAgreement I σ W coin)) ≤
      p.rankError + L/(Nat.card F : ℚ) := by
  have hlow : p.overlapSize < a := by
    have h := (le_max_left _ _).trans hlarge
    change I.r+I.w+I.s+I.s+1 ≤ a at h
    change I.r+I.w+2*I.s-1 < a
    omega
  have hcard : ((capacityTail I W a).card : ℚ) ≤ L :=
    (Nat.cast_le (α := ℚ)).mpr (capacityTail_card_le I p W a L hlow hbound)
  have hdiv : (capacityTail I W a).card/(Nat.card F : ℚ) ≤ L/(Nat.card F : ℚ) :=
    div_le_div_of_nonneg_right hcard (by positivity)
  exact (maxFailureAgreement_tail_le I p σ W hlarge).trans (add_le_add le_rfl hdiv)

/-- Complete tail profile, including the levels below recovery's floor. -/
noncomputable def failureAgreementTail (I : Instance F) (p : ProfileParameters I)
    (listBound : ℕ → ℕ) (a : ℕ) : ℚ :=
  if p.largeSize ≤ a then min 1 (p.rankError + listBound a/(Nat.card F : ℚ)) else 1

theorem maxFailureAgreement_tail_le_profile (I : Instance F) (p : ProfileParameters I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (listBound : ℕ → ℕ)
    (hbound : ∀ a, p.largeSize ≤ a → a ≤ I.n →
      CodingTheory.UniformFamilyBound I.n a p.overlapSize (listBound a))
    (a : ℕ) (han : a ≤ I.n) :
    mean (fun coin : I.layer.Coin => indicator (a ≤ maxFailureAgreement I σ W coin)) ≤
      failureAgreementTail I p listBound a := by
  have hunit : mean (fun coin : I.layer.Coin => indicator (a ≤ maxFailureAgreement I σ W coin)) ≤ 1 := by
    have hm := mean_mono (fun coin : I.layer.Coin =>
      (show indicator (a ≤ maxFailureAgreement I σ W coin) ≤ 1 by
        unfold indicator
        split_ifs <;> norm_num))
    exact hm.trans_eq (mean_const 1)
  unfold failureAgreementTail
  split_ifs with hlarge
  · exact le_min hunit (maxFailureAgreement_tail_le_of_uniformFamilyBound
      I p σ W a (listBound a) hlarge (hbound a hlarge han))
  · exact hunit

/-- V1's layer-cake theorem transfers the complete tail to every monotone
curve, without selecting a single agreement threshold. -/
theorem failure_potential_mean_le (I : Instance F) (p : ProfileParameters I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (ψ : PotentialProfile.Curve I.n)
    (listBound : ℕ → ℕ)
    (hbound : ∀ a, p.largeSize ≤ a → a ≤ I.n →
      CodingTheory.UniformFamilyBound I.n a p.overlapSize (listBound a)) :
    mean (fun coin : I.layer.Coin => ψ.value (maxFailureAgreement I σ W coin)) ≤
      ∑ a ∈ range (I.n+1), ψ.increment a * failureAgreementTail I p listBound a := by
  apply ψ.mean_le_tail_sum (maxFailureAgreement I σ W) (maxFailureAgreement_le I σ W)
  intro a han
  have ht := maxFailureAgreement_tail_le_profile I p σ W listBound hbound a han
  rw [mean_indicator] at ht
  convert! ht using 1
  congr 2
  apply congrArg Finset.card
  ext coin
  simp only [AgreementProfile.tailSet, mem_filter, mem_univ, true_and]

/-- The challenge's raw hash-answer charge uses V1's exact decoder-balance
lemma, retaining the role's fiber factor. -/
theorem failure_challenge_hash_charge_le (I : Instance F) (p : ProfileParameters I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (ψ : PotentialProfile.Curve I.n)
    (listBound : ℕ → ℕ)
    (hbound : ∀ a, p.largeSize ≤ a → a ≤ I.n →
      CodingTheory.UniformFamilyBound I.n a p.overlapSize (listBound a))
    {C : Type} [Fintype C] (decode : C → I.layer.Coin) (k : ℕ)
    (hbalance : ∀ coin, (univ.filter fun c : C => decode c = coin).card ≤ k) :
    (∑ c : C, ψ.value (maxFailureAgreement I σ W (decode c))) ≤
      k * Fintype.card I.layer.Coin *
        (∑ a ∈ range (I.n+1), ψ.increment a * failureAgreementTail I p listBound a) := by
  exact LfzkV1.ZkPotentialBalance.decoded_mean_le decode
    (fun coin => ψ.value (maxFailureAgreement I σ W coin))
    (fun coin => ψ.nonneg _ (maxFailureAgreement_le I σ W coin)) k hbalance _
    (failure_potential_mean_le I p σ W ψ listBound hbound)

theorem failureQueries_card_le_maxAgreement (I : Instance F) (σ : I.layer.Statement) (W : I.layer.Oracle)
    (coin : I.layer.Coin) (response : I.layer.Payload) :
    (univ.filter fun query : I.layer.Query => I.layer.verify σ W coin response query ∧
      scanRecoverAt I σ W coin response = none).card ≤ (maxFailureAgreement I σ W coin).choose I.t := by
  let allowed := failureCoordinates I σ W coin response
  have hsub : (univ.filter fun query : I.layer.Query => I.layer.verify σ W coin response query ∧
      scanRecoverAt I σ W coin response = none) ⊆ queriesWithin allowed := by
    intro query hquery
    have h := (mem_filter.mp hquery).2
    have hv := (verify_openOracle_iff I.domain (by have := I.primary_le; omega)
      I.primary_le I.layout σ W coin response query).mp h.1
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    change query.coordinates ⊆ failureCoordinates I σ W coin response
    rw [failureCoordinates,if_pos ⟨h.2,hv.1⟩]
    exact hv.2
  have hsize : allowed.card ≤ maxFailureAgreement I σ W coin :=
    Finset.le_sup (f := fun response : I.layer.Payload =>
      (failureCoordinates I σ W coin response).card) (mem_univ response)
  exact ((card_le_card hsub).trans (card_queriesWithin_le allowed le_rfl)).trans
    (Nat.choose_le_choose I.t hsize)

/-- The query-stage inequality is exactly V1's residual potential argument,
applied to Polygero's actual verifier and complete response. -/
theorem failure_query_positive_increase_le (I : Instance F) (σ : I.layer.Statement) (W : I.layer.Oracle)
    (ψ : PotentialProfile.Curve I.n) (coin : I.layer.Coin) (response : I.layer.Payload) :
    (1-ψ.value (maxFailureAgreement I σ W coin)) *
      (((univ.filter fun query : I.layer.Query => I.layer.verify σ W coin response query ∧
        scanRecoverAt I σ W coin response = none).card : ℚ) / I.n.choose I.t) ≤
      ψ.queryCost (fun a => hypergeometricRatio a I.n I.t) := by
  let a := maxFailureAgreement I σ W coin
  have ha : a ≤ I.n := maxFailureAgreement_le I σ W coin
  have hfirst : ((univ.filter fun query : I.layer.Query => I.layer.verify σ W coin response query ∧
      scanRecoverAt I σ W coin response = none).card : ℚ) / I.n.choose I.t ≤
      hypergeometricRatio a I.n I.t := by
    unfold hypergeometricRatio
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast failureQueries_card_le_maxAgreement I σ W coin response) (Nat.cast_nonneg _)
  have hnonneg : 0 ≤ 1-ψ.value a := sub_nonneg.mpr (ψ.le_one a ha)
  have hcharge := mul_le_mul_of_nonneg_left hfirst hnonneg
  apply hcharge.trans
  unfold PotentialProfile.Curve.queryCost
  rw [Finset.le_sup'_iff]
  exact ⟨a,mem_range.mpr (by omega),le_rfl⟩

/-- V1's existing balance lemma transports the residual charge to the full
hash-answer space without rounding the potential to a Boolean event. -/
theorem failure_query_hash_charge_le (I : Instance F) (σ : I.layer.Statement) (W : I.layer.Oracle)
    (ψ : PotentialProfile.Curve I.n) (coin : I.layer.Coin) (response : I.layer.Payload)
    {C : Type} [Fintype C] [DecidableEq I.layer.Query]
    (decode : C → I.layer.Query) (k : ℕ)
    (hbalance : ∀ query, (univ.filter fun c : C => decode c = query).card ≤ k) :
    (∑ c : C, if I.layer.verify σ W coin response (decode c) ∧ scanRecoverAt I σ W coin response = none
      then 1-ψ.value (maxFailureAgreement I σ W coin) else 0) ≤
      k * Fintype.card I.layer.Query * ψ.queryCost (fun a => hypergeometricRatio a I.n I.t) := by
  apply LfzkV1.ZkPotentialBalance.decoded_query_charge_le decode
    (fun query : I.layer.Query => I.layer.verify σ W coin response query ∧ scanRecoverAt I σ W coin response = none)
    (1-ψ.value (maxFailureAgreement I σ W coin))
    (sub_nonneg.mpr (ψ.le_one _ (maxFailureAgreement_le I σ W coin))) k hbalance
  rw [show Fintype.card I.layer.Query = I.n.choose I.t from QuerySet.fintype_card _ _]
  exact failure_query_positive_increase_le I σ W ψ coin response

/-- In V1's terminal doom branch the built statement has no satisfying
member in the committed list. A decoded response is then outside that list;
an undecoded response uses the graded failure bound. -/
theorem query_positive_increase_le_of_noSat (I : Instance F) (σ : I.layer.Statement)
    (W : I.layer.Oracle) (ψ : PotentialProfile.Curve I.n) (cutoff : ℕ)
    (hnosat : ∀ g ∈ Counting.committedCandidates I W cutoff,
      ¬ I.layer.satisfies σ ((Counting.tupleCounts I).witness g))
    (coin : I.layer.Coin) (response : I.layer.Payload) :
    (1-ψ.value (maxFailureAgreement I σ W coin)) *
        (((univ.filter (I.layer.verify σ W coin response)).card : ℚ) / I.n.choose I.t) ≤
      max (ψ.queryCost (fun a => hypergeometricRatio a I.n I.t))
        (((cutoff+I.s-1).choose I.t : ℚ)/I.n.choose I.t) := by
  cases hdecode : scanRecoverAt I σ W coin response with
  | none =>
    have h := failure_query_positive_increase_le I σ W ψ coin response
    simp only [hdecode, and_true] at h
    exact h.trans (le_max_left _ _)
  | some g =>
    have hout : g ∉ Counting.committedCandidates I W cutoff :=
      fun hg => hnosat g hg (scanRecoverAt_valid I σ W coin response g hdecode)
    have hfrac := Counting.fraction_le_of_decoded_not_mem I σ W coin response g cutoff hdecode hout
    have hψ : 0 ≤ ψ.value (maxFailureAgreement I σ W coin) :=
      ψ.nonneg _ (maxFailureAgreement_le I σ W coin)
    have hnonneg : 0 ≤ fraction I σ W coin response := by unfold fraction; positivity
    have hleft : (1-ψ.value (maxFailureAgreement I σ W coin)) * fraction I σ W coin response ≤
        fraction I σ W coin response := by nlinarith only [mul_nonneg hψ hnonneg]
    have hcard : Fintype.card I.layer.Query = I.n.choose I.t := QuerySet.fintype_card _ _
    simpa only [fraction, Counting.responseCount, hcard] using
      hleft.trans (hfrac.trans (le_max_right _ _))

theorem query_hash_charge_le_of_noSat (I : Instance F) (σ : I.layer.Statement)
    (W : I.layer.Oracle) (ψ : PotentialProfile.Curve I.n) (cutoff : ℕ)
    (hnosat : ∀ g ∈ Counting.committedCandidates I W cutoff,
      ¬ I.layer.satisfies σ ((Counting.tupleCounts I).witness g))
    (coin : I.layer.Coin) (response : I.layer.Payload)
    {C : Type} [Fintype C] (decode : C → I.layer.Query) (k : ℕ)
    (hbalance : ∀ query, (univ.filter fun c : C => decode c = query).card ≤ k) :
    (∑ c : C, if I.layer.verify σ W coin response (decode c) then
      1-ψ.value (maxFailureAgreement I σ W coin) else 0) ≤
      k * Fintype.card I.layer.Query *
        max (ψ.queryCost (fun a => hypergeometricRatio a I.n I.t))
          (((cutoff+I.s-1).choose I.t : ℚ)/I.n.choose I.t) := by
  apply LfzkV1.ZkPotentialBalance.decoded_query_charge_le decode
    (I.layer.verify σ W coin response) (1-ψ.value (maxFailureAgreement I σ W coin))
    (sub_nonneg.mpr (ψ.le_one _ (maxFailureAgreement_le I σ W coin))) k hbalance
  rw [show Fintype.card I.layer.Query = I.n.choose I.t from QuerySet.fintype_card _ _]
  exact query_positive_increase_le_of_noSat I σ W ψ cutoff hnosat coin response

/-- V1's two terminal obligations, specialized to the Polygero verifier.
The statement and oracle are fixed before its challenge; the complete
response may be chosen afterwards. Budgets count raw hash answers. -/
structure TerminalPotential (I : Instance F) {C : Type} [Fintype C] (cutoff : ℕ)
    (decodeCoin : C → I.layer.Coin) (decodeQuery : C → I.layer.Query) where
  weight : I.layer.Statement → I.layer.Oracle → I.layer.Coin → ℚ
  nonneg : ∀ σ W coin, 0 ≤ weight σ W coin
  le_one : ∀ σ W coin, weight σ W coin ≤ 1
  challengeBudget : ℚ
  queryBudget : ℚ
  challengeBudget_nonneg : 0 ≤ challengeBudget
  queryBudget_nonneg : 0 ≤ queryBudget
  challenge_le : ∀ σ W, (∑ c : C, weight σ W (decodeCoin c)) ≤ challengeBudget
  query_le : ∀ σ W,
    (∀ g ∈ Counting.committedCandidates I W cutoff,
      ¬ I.layer.satisfies σ ((Counting.tupleCounts I).witness g)) →
    ∀ coin response, (∑ c : C, if I.layer.verify σ W coin response (decodeQuery c) then
      1-weight σ W coin else 0) ≤ queryBudget

/-- The checked recovery and packing tails instantiate the same graded
terminal data as V1, using its curve and decoder-balance lemmas. -/
noncomputable def terminalPotential (I : Instance F) (p : ProfileParameters I)
    (ψ : PotentialProfile.Curve I.n) (cutoff : ℕ) (listBound : ℕ → ℕ)
    (hbound : ∀ a, p.largeSize ≤ a → a ≤ I.n →
      CodingTheory.UniformFamilyBound I.n a p.overlapSize (listBound a))
    {C : Type} [Fintype C] (decodeCoin : C → I.layer.Coin) (decodeQuery : C → I.layer.Query)
    (kCoin kQuery : ℕ)
    (hcoin : ∀ coin, (univ.filter fun c : C => decodeCoin c = coin).card ≤ kCoin)
    (hquery : ∀ query, (univ.filter fun c : C => decodeQuery c = query).card ≤ kQuery) :
    TerminalPotential I cutoff decodeCoin decodeQuery where
  weight σ W coin := ψ.value (maxFailureAgreement I σ W coin)
  nonneg σ W coin := ψ.nonneg _ (maxFailureAgreement_le I σ W coin)
  le_one σ W coin := ψ.le_one _ (maxFailureAgreement_le I σ W coin)
  challengeBudget := max 0 (kCoin * Fintype.card I.layer.Coin *
    (∑ a ∈ range (I.n+1), ψ.increment a * failureAgreementTail I p listBound a))
  queryBudget := max 0 (kQuery * Fintype.card I.layer.Query *
    max (ψ.queryCost (fun a => hypergeometricRatio a I.n I.t))
      (((cutoff+I.s-1).choose I.t : ℚ)/I.n.choose I.t))
  challengeBudget_nonneg := le_max_left _ _
  queryBudget_nonneg := le_max_left _ _
  challenge_le σ W := (failure_challenge_hash_charge_le I p σ W ψ listBound hbound
    decodeCoin kCoin hcoin).trans (le_max_right _ _)
  query_le σ W hnosat coin response := (query_hash_charge_le_of_noSat
    I σ W ψ cutoff hnosat coin response decodeQuery kQuery hquery).trans (le_max_right _ _)

end RecursivePolygero.NonrecursiveFS
