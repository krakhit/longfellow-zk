import LfzkV2.RuntimeCost
import LfzkV1.TSec

/-! Work-normalized comparisons for the instantiated two-field bound.
Eight Merkle queries cover the startup cost at 117 bits, including the
verifier lookup. RawRuntimeExtraction handles smaller Merkle budgets by
counting predictable digest hits. -/

namespace LfzkV2.Replay

theorem layerSlots_le_sharpBudget {F : Type} {out input : ℕ} (circuit : Circuit F out input) :
    layerSlots circuit ≤ circuit.sharpLayerBudget := by
  induction circuit with
  | input => exact le_rfl
  | @layer out mid input a body rest ih =>
      have hv : vectorSlots a = min 1 a := by cases a <;> simp [vectorSlots]
      change vectorSlots a+mid+1+layerSlots rest ≤ min 1 a+2*mid+1+rest.sharpLayerBudget
      rw [hv]
      omega

theorem slots_le_budget {F : Type} {out input : ℕ} (circuit : Circuit F out input) :
    slots circuit ≤ out+circuit.sharpLayerBudget := by
  have hv : vectorSlots out ≤ out := by cases out <;> simp [vectorSlots]
  exact Nat.add_le_add hv (layerSlots_le_sharpBudget circuit)

end LfzkV2.Replay

namespace LfzkV2.RuntimeSecurity

open RuntimeCost

theorem slots_le {F₁ F₂ : Type} {out₁ input₁ out₂ input₂ : ℕ}
    (circuit₁ : Circuit F₁ out₁ input₁) (circuit₂ : Circuit F₂ out₂ input₂)
    (hfront₁ : out₁+circuit₁.sharpLayerBudget ≤ 655) (hfront₂ : out₂+circuit₂.sharpLayerBudget ≤ 552) :
    1+(Replay.slots circuit₁+2)+(Replay.slots circuit₂+2) ≤ 1212 := by
  have h₁ := (Replay.slots_le_budget circuit₁).trans hfront₁
  have h₂ := (Replay.slots_le_budget circuit₂).trans hfront₂
  omega

private theorem numerator_le {N tA L G : ℕ} (hL : L ≤ 1212) (htA : tA ≤ G) :
    Bcs.AdaptiveCommit.adaptiveNumerator 12992 tA (L+N) ≤
      12992*(1+1212)+N*(12992+G)+tA*(3*G+2*12992+1+1212) := by
  apply (LfzkV1.TSec.adaptiveNumerator_le_linear (fc := 12992) (L := L) (N := N) htA).trans
  gcongr

theorem slack_114 :
    constant+2*((12992*(1+1212) : ℕ) : ℚ)/(2^256 : ℚ) ≤ 1/(2^114 : ℚ) ∧
    coefficient+2*((12992+2^114 : ℕ) : ℚ)/(2^256 : ℚ) ≤ 1/(2^114 : ℚ) ∧
    2*((3*2^114+2*12992+1+1212 : ℕ) : ℚ)/(2^256 : ℚ) ≤ 1/(2^114 : ℚ) := by
  norm_num [constant,coefficient]

/-- A conservative all-budget certificate for the complete two-field RHS,
including both Merkle explanation errors. The underlying probability must
be bounded by the actual instantiated extraction theorem. -/
theorem tsec_114 {p : ℚ} {N tA L : ℕ} (hp₁ : p ≤ 1) (hL : L ≤ 1212)
    (hp : p ≤ N*coefficient+constant+
      2*(Bcs.AdaptiveCommit.adaptiveNumerator 12992 tA (L+N) : ℚ)/(2^256 : ℚ)) :
    p ≤ (1+N+tA : ℚ)/(2^114 : ℚ) := by
  have hbound : p ≤ constant+N*coefficient+
      2*(Bcs.AdaptiveCommit.adaptiveNumerator 12992 tA (L+N) : ℚ)*(1/(2^256 : ℚ)) := by
    convert! hp using 1
    ring
  have hA : constant+2*((12992*(1+L) : ℕ) : ℚ)/(2^256 : ℚ) ≤ 1/(2^114 : ℚ) := by
    apply le_trans _ slack_114.1
    gcongr
  have hT : 2*((3*2^114+2*12992+1+L : ℕ) : ℚ)/(2^256 : ℚ) ≤ 1/(2^114 : ℚ) := by
    apply le_trans _ slack_114.2.2
    gcongr
  have h := LfzkV1.TSec.tsec_of_linear_slack (fc := 12992) (L := L) (G := 2^114)
    (A := constant) (K := coefficient) (δ := 1/(2^256 : ℚ)) (k := 2) (ε := 1/(2^114 : ℚ))
    hp₁ hbound (by positivity) (by norm_num) (by positivity)
    (by simpa only [mul_one_div] using hA)
    (by simpa only [mul_one_div] using slack_114.2.1)
    (by simpa only [mul_one_div] using hT) (by norm_num)
  simpa only [mul_one_div] using h

theorem slack_117 :
    constant+2*((12992*(1+1212) : ℕ) : ℚ)/(2^256 : ℚ) +
      11*(coefficient+2*((12992+2^117 : ℕ) : ℚ)/(2^256 : ℚ)) ≤ 12/(2^117 : ℚ) ∧
    coefficient+2*((12992+2^117 : ℕ) : ℚ)/(2^256 : ℚ) ≤ 1/(2^117 : ℚ) ∧
    2*((3*2^117+2*12992+1+1212 : ℕ) : ℚ)/(2^256 : ℚ) ≤ 1/(2^117 : ℚ) := by
  norm_num [constant,coefficient]

/-- The current graded profile attains the 117-bit work-normalized bound
for N ≥ 11, for arbitrary Merkle-query budgets. The explicit lower bound
on N is retained: this theorem is not the full target certificate. -/
theorem tsec_117_of_ge {p : ℚ} {N tA L : ℕ} (hp₁ : p ≤ 1) (hL : L ≤ 1212) (hN : 11 ≤ N)
    (hp : p ≤ N*coefficient+constant+
      2*(Bcs.AdaptiveCommit.adaptiveNumerator 12992 tA (L+N) : ℚ)/(2^256 : ℚ)) :
    p ≤ (1+N+tA : ℚ)/(2^117 : ℚ) := by
  by_cases htA : tA ≤ 2^117
  · let A : ℚ := constant+2*((12992*(1+1212) : ℕ) : ℚ)/(2^256 : ℚ)
    let K : ℚ := coefficient+2*((12992+2^117 : ℕ) : ℚ)/(2^256 : ℚ)
    let T : ℚ := 2*((3*2^117+2*12992+1+1212 : ℕ) : ℚ)/(2^256 : ℚ)
    have hcount : (Bcs.AdaptiveCommit.adaptiveNumerator 12992 tA (L+N) : ℚ) ≤
        ((12992*(1+1212) : ℕ) : ℚ)+(N : ℚ)*((12992+2^117 : ℕ) : ℚ)+
          (tA : ℚ)*((3*2^117+2*12992+1+1212 : ℕ) : ℚ) := by
      exact_mod_cast numerator_le hL htA
    have hprob : p ≤ A+N*K+tA*T := by
      calc
        p ≤ N*coefficient+constant+
            2*(Bcs.AdaptiveCommit.adaptiveNumerator 12992 tA (L+N) : ℚ)/(2^256 : ℚ) := hp
        _ ≤ N*coefficient+constant+2*
            (((12992*(1+1212) : ℕ) : ℚ)+(N : ℚ)*((12992+2^117 : ℕ) : ℚ)+
              (tA : ℚ)*((3*2^117+2*12992+1+1212 : ℕ) : ℚ))/(2^256 : ℚ) := by gcongr
        _ = A+N*K+tA*T := by dsimp only [A,K,T]; ring
    have hbase : A+11*K ≤ 12/(2^117 : ℚ) := slack_117.1
    have hslope : K ≤ 1/(2^117 : ℚ) := slack_117.2.1
    have hmerkle : T ≤ 1/(2^117 : ℚ) := slack_117.2.2
    have hNq : (11 : ℚ) ≤ N := by exact_mod_cast hN
    have hstep := mul_le_mul_of_nonneg_left hslope (sub_nonneg.mpr hNq)
    have htstep := mul_le_mul_of_nonneg_left hmerkle (Nat.cast_nonneg tA : (0 : ℚ) ≤ tA)
    have h : p ≤ (1+N+tA : ℚ)*(1/(2^117 : ℚ)) := by
      calc
        p ≤ A+N*K+tA*T := hprob
        _ = (A+11*K)+(N-11 : ℚ)*K+tA*T := by ring
        _ ≤ 12/(2^117 : ℚ)+(N-11 : ℚ)*(1/(2^117 : ℚ))+(tA : ℚ)*(1/(2^117 : ℚ)) :=
          add_le_add (add_le_add hbase hstep) htstep
        _ = (1+N+tA : ℚ)*(1/(2^117 : ℚ)) := by ring
    simpa only [mul_one_div] using h
  · apply hp₁.trans
    apply (le_div_iff₀ (by positivity : (0 : ℚ) < 2^117)).mpr
    have hlarge : (2^117 : ℚ) ≤ tA := by exact_mod_cast (by omega : 2^117 ≤ tA)
    have hnonneg : (0 : ℚ) ≤ N := Nat.cast_nonneg _
    linarith

/-- Eight Merkle queries pay for the finite startup cost, including the
verifier's additional transcript lookup. Smaller Merkle budgets are handled
by bounding authenticated acceptance itself. -/
theorem tsec_117_of_merkle_ge {p : ℚ} {N tA L : ℕ}
    (hp₁ : p ≤ 1) (hL : L ≤ 1212) (ht : 8 ≤ tA)
    (hp : p ≤ (1+N : ℕ)*coefficient+constant+
      2*(Bcs.AdaptiveCommit.adaptiveNumerator 12992 tA (L+(1+N)) : ℚ)/(2^256 : ℚ)) :
    p ≤ (1+N+tA : ℚ)/(2^117 : ℚ) := by
  by_cases htA : tA ≤ 2^117
  · let A : ℚ := constant+coefficient+2*((12992*(1+1213) : ℕ) : ℚ)/(2^256 : ℚ)
    let K : ℚ := coefficient+2*((12992+2^117 : ℕ) : ℚ)/(2^256 : ℚ)
    let T : ℚ := 2*((3*2^117+2*12992+1+1213 : ℕ) : ℚ)/(2^256 : ℚ)
    have hcountNat : Bcs.AdaptiveCommit.adaptiveNumerator 12992 tA (L+(1+N)) ≤
        12992*(1+1213)+N*(12992+2^117)+tA*(3*2^117+2*12992+1+1213) := by
      rw [show L+(1+N) = (L+1)+N by omega]
      apply (LfzkV1.TSec.adaptiveNumerator_le_linear
        (fc := 12992) (L := L+1) (N := N) htA).trans
      gcongr <;> omega
    have hcount : (Bcs.AdaptiveCommit.adaptiveNumerator 12992 tA (L+(1+N)) : ℚ) ≤
        ((12992*(1+1213) : ℕ) : ℚ)+(N : ℚ)*((12992+2^117 : ℕ) : ℚ)+
          (tA : ℚ)*((3*2^117+2*12992+1+1213 : ℕ) : ℚ) := by
      exact_mod_cast hcountNat
    have hprob : p ≤ A+N*K+tA*T := by
      calc
        p ≤ (1+N : ℕ)*coefficient+constant+
            2*(Bcs.AdaptiveCommit.adaptiveNumerator 12992 tA (L+(1+N)) : ℚ)/(2^256 : ℚ) := hp
        _ ≤ (1+N : ℕ)*coefficient+constant+2*
            (((12992*(1+1213) : ℕ) : ℚ)+(N : ℚ)*((12992+2^117 : ℕ) : ℚ)+
              (tA : ℚ)*((3*2^117+2*12992+1+1213 : ℕ) : ℚ))/(2^256 : ℚ) := by gcongr
        _ = A+N*K+tA*T := by dsimp only [A,K,T]; push_cast; ring
    have hbase : A+8*T ≤ 9/(2^117 : ℚ) := by norm_num [A,T,constant,coefficient]
    have hslope : K ≤ 1/(2^117 : ℚ) := by norm_num [K,coefficient]
    have hmerkle : T ≤ 1/(2^117 : ℚ) := by norm_num [T]
    have htq : (8 : ℚ) ≤ tA := by exact_mod_cast ht
    have hstep := mul_le_mul_of_nonneg_left hslope (Nat.cast_nonneg N : (0 : ℚ) ≤ N)
    have htstep := mul_le_mul_of_nonneg_left hmerkle (sub_nonneg.mpr htq)
    have h : p ≤ (1+N+tA : ℚ)*(1/(2^117 : ℚ)) := by
      calc
        p ≤ A+N*K+tA*T := hprob
        _ = (A+8*T)+N*K+(tA-8 : ℚ)*T := by ring
        _ ≤ 9/(2^117 : ℚ)+(N : ℚ)*(1/(2^117 : ℚ))+
            (tA-8 : ℚ)*(1/(2^117 : ℚ)) := add_le_add (add_le_add hbase hstep) htstep
        _ = (1+N+tA : ℚ)*(1/(2^117 : ℚ)) := by ring
    simpa only [mul_one_div] using h
  · apply hp₁.trans
    apply (le_div_iff₀ (by positivity : (0 : ℚ) < 2^117)).mpr
    have hlarge : (2^117 : ℚ) ≤ tA := by exact_mod_cast (by omega : 2^117 ≤ tA)
    have hnonneg : (0 : ℚ) ≤ N := Nat.cast_nonneg _
    linarith

end LfzkV2.RuntimeSecurity
