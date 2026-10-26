import polygero.Local.CommittedCandidates
import polygero.FiatShamir.Budgets
import Bcs.SingleQuery

/-! Adaptive opening-query search cannot avoid the committed witness list
without paying its exact binomial tail. -/

noncomputable section
namespace RecursivePolygero.NonrecursiveFS
open Finset Counting Bcs.TotalOracle Merkle.RandomOracle
open scoped Classical
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

def decodedOutsideList (I : Instance F) (σ : I.layer.Statement) (W : I.layer.Oracle)
    (coin : I.layer.Coin) (payload : I.layer.Payload) (cutoff : ℕ) : Prop :=
  ∃ g, scanRecoverAt I σ W coin payload = some g ∧ g ∉ committedCandidates I W cutoff

theorem decoded_outside_query_raw_le (I : Instance F)
    {C : Type} [Fintype C] [DecidableEq I.layer.Query]
    (decodeQuery : C → I.layer.Query) (kQuery : ℕ)
    (hquery : ∀ query, (univ.filter fun b : C => decodeQuery b = query).card ≤ kQuery)
    (hkQuery : kQuery*Fintype.card I.layer.Query ≤ Fintype.card C)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin)
    (payload : I.layer.Payload) (cutoff : ℕ) :
    (∑ b : C, if I.layer.verify σ W coin payload (decodeQuery b) ∧
      decodedOutsideList I σ W coin payload cutoff then (1 : ℚ) else 0) ≤
      Fintype.card C * (((cutoff+I.s-1).choose I.t : ℚ)/I.n.choose I.t) := by
  by_cases hb : decodedOutsideList I σ W coin payload cutoff
  · obtain ⟨g, hg, hout⟩ := hb
    have hmean := (query_mean I σ W coin payload).le.trans
      (fraction_le_of_decoded_not_mem I σ W coin payload g cutoff hg hout)
    have h := balanced_sum_le decodeQuery kQuery hquery hkQuery
      (fun query => indicator (I.layer.verify σ W coin payload query))
      (fun _ => indicator_nonneg _) _ (by positivity) hmean
    convert! h using 1
    apply sum_congr rfl
    intro b _
    simp only [indicator, and_true, show decodedOutsideList I σ W coin payload cutoff from ⟨g,hg,hout⟩]
  · simp only [hb, and_false, if_false, sum_const_zero]
    positivity

/-- The list and statement can depend on earlier transcript answers. The
complete response names the terminal hash point, so its held-out coordinate
does not change the context, batching coin, or decoded witness. -/
theorem decoded_outside_list_le (I : Instance F)
    {C Pt Out Parent State : Type}
    [Fintype C] [Nonempty C] [Fintype Pt] [DecidableEq Pt]
    {N : ℕ} (tree : Tree Pt C Out N) (selected : Out → Parent × I.layer.Payload)
    (parent : Parent → Pt) (child : Parent → I.layer.Payload → Pt)
    (hchild : Function.Injective (fun i : Parent × I.layer.Payload => child i.1 i.2))
    (hdisjoint : ∀ j payload, parent j ≠ child j payload)
    (state : Parent → (Pt → C) → State)
    (hstateOff : ∀ j payload H H', AgreeOff (child j payload) H H' → state j H = state j H')
    (statement : State → Parent → I.layer.Statement)
    (oracle : State → Parent → I.layer.Oracle)
    [DecidableEq I.layer.Query]
    (decodeCoin : C → I.layer.Coin) (decodeQuery : C → I.layer.Query)
    (kQuery : ℕ)
    (hquery : ∀ query, (univ.filter fun b : C => decodeQuery b = query).card ≤ kQuery)
    (hkQuery : kQuery*Fintype.card I.layer.Query ≤ Fintype.card C) (cutoff : ℕ) :
    let failure := fun H : Pt → C =>
      let i := selected (tree.run H).1
      let σ := statement (state i.1 H) i.1
      let W := oracle (state i.1 H) i.1
      let coin := decodeCoin (H (parent i.1))
      I.layer.verify σ W coin i.2 (decodeQuery (H (child i.1 i.2))) ∧
        decodedOutsideList I σ W coin i.2 cutoff
    ((univ.filter failure).card : ℚ)/(Fintype.card C : ℚ)^Fintype.card Pt ≤
      (N+1 : ℕ)*(((cutoff+I.s-1).choose I.t : ℚ)/I.n.choose I.t) := by
  intro failure
  let entry := fun x : Pt => if h : ∃ i : Parent × I.layer.Payload, child i.1 i.2 = x
    then some h.choose else none
  have hentry x i (he : entry x = some i) : child i.1 i.2 = x := by
    dsimp only [entry] at he
    split_ifs at he with hx
    · cases Option.some.inj he
      exact hx.choose_spec
  have hentryChild (i : Parent × I.layer.Payload) : entry (child i.1 i.2) = some i := by
    have hx : ∃ j : Parent × I.layer.Payload, child j.1 j.2 = child i.1 i.2 := ⟨i,rfl⟩
    simp only [entry, dif_pos hx]
    congr 1
    exact hchild hx.choose_spec
  let localEvent := fun x (H : Pt → C) c => match entry x with
    | none => False
    | some i =>
      let σ := statement (state i.1 H) i.1
      let W := oracle (state i.1 H) i.1
      let coin := decodeCoin (H (parent i.1))
      I.layer.verify σ W coin i.2 (decodeQuery c) ∧ decodedOutsideList I σ W coin i.2 cutoff
  have hoff x H H' (h : AgreeOff x H H') c : localEvent x H c ↔ localEvent x H' c := by
    cases he : entry x with
    | none => simp only [localEvent, he]
    | some i =>
        have hx := hentry x i he
        have hs := hstateOff i.1 i.2 H H' (by simpa only [hx] using h)
        have hp := h (parent i.1) (fun hh => hdisjoint i.1 i.2 (hh.trans hx.symm))
        simp only [localEvent, he, hs, hp]
  have hlocal x H : (∑ c : C, if localEvent x H c then (1 : ℚ) else 0) ≤
      Fintype.card C * (((cutoff+I.s-1).choose I.t : ℚ)/I.n.choose I.t) := by
    cases he : entry x with
    | none => simp only [localEvent, he, if_false, sum_const_zero]; positivity
    | some i =>
        simpa only [localEvent, he] using decoded_outside_query_raw_le I decodeQuery kQuery hquery hkQuery
          (statement (state i.1 H) i.1) (oracle (state i.1 H) i.1)
          (decodeCoin (H (parent i.1))) i.2 cutoff
  convert! tree_final_event_ratio_le tree (fun out => child (selected out).1 (selected out).2)
    localEvent hoff _ (by positivity) hlocal failure (by
      intro H hH
      simpa only [localEvent, hentryChild] using hH) using 1
  congr 3
  ext H
  simp only [mem_filter]

end RecursivePolygero.NonrecursiveFS
