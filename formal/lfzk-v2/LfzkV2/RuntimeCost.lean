import LfzkV2.GradedCost
import LfzkV2.RuntimeSide

/-! A conservative numerical instantiation of the actual two-field cost.
The larger signature field is retained throughout. RuntimeExtraction and
RawRuntimeExtraction turn this affine cost into finite work-normalized
bounds, including an all-budget unit-offset 117-bit endpoint. -/

namespace LfzkV2.RuntimeCost

open Finset RecursivePolygero TwoFieldReplay RuntimeProfiles

def coefficient : ℚ := 737/(2^128 : ℚ)
def constant : ℚ := 16383/(2^128 : ℚ)+18460/(2^255 : ℚ)

private theorem div_nat_le {a b q q₀ : ℕ} (hq₀ : 0 < q₀) (hab : a ≤ b) (hq : q₀ ≤ q) :
    (a : ℚ)/q ≤ (b : ℚ)/q₀ := by
  have hqpos : (0 : ℚ) < q₀ := by exact_mod_cast hq₀
  exact (div_le_div_of_nonneg_right (by exact_mod_cast hab) (Nat.cast_nonneg q)).trans
    (div_le_div_of_nonneg_left (Nat.cast_nonneg b) hqpos (by exact_mod_cast hq))

private theorem mac_rate_le {Fmac : Type} [Fintype Fmac]
    (hmac : 2^128 ≤ Fintype.card Fmac) :
    (22 : ℚ)*33/Fintype.card Fmac ≤ 726/(2^128 : ℚ) := by
  simpa only [Nat.cast_pow,Nat.cast_ofNat,show (22 : ℚ)*33 = 726 by norm_num] using
    (div_nat_le (a := 726) (b := 726) (q₀ := 2^128) (by decide) le_rfl hmac)

variable {F₁ F₂ Key C Public Fmac : Type}
variable [Field F₁] [Fintype F₁] [DecidableEq F₁]
variable [Field F₂] [Fintype F₂] [DecidableEq F₂] [Fintype C] [Nonempty C]
variable [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {blocks : ℕ}
variable {out₁ input₁ out₂ input₂ : ℕ}
variable (circuit₁ : Circuit F₁ out₁ input₁) (I₁ : Instance F₁)
variable (circuit₂ : Circuit F₂ out₂ input₂) (I₂ : Instance F₂)
variable (S₁ : CompiledSide F₁ C (SideContext Key C Public) circuit₁ I₁)
variable (S₂ : CompiledSide F₂ C
  (SideContext Key C Public × FirstSnapshot Key C Public circuit₁ I₁) circuit₂ I₂)
variable (geometry₁ : Geometry Hash.profile I₁) (geometry₂ : Geometry Signature.profile I₂)
variable (sampling₁ : BackendSampling I₁ S₁.decodeCoin S₁.decodeQuery)
variable (sampling₂ : BackendSampling I₂ S₂.decodeCoin S₂.decodeQuery)

theorem terminal_rates (hfield₁ : 2^128 ≤ Fintype.card F₁) (hfield₂ : 2^255 ≤ Fintype.card F₂) :
    let T₁ := S₁.withProfile Hash.profile geometry₁ sampling₁
    let T₂ := S₂.withProfile Signature.profile geometry₂ sampling₂
    (T₁.potential.challengeBudget/Fintype.card C ≤ 51/(2^128 : ℚ) ∧
      T₁.potential.queryBudget/Fintype.card C ≤ 737/(2^128 : ℚ)) ∧
    (T₂.potential.challengeBudget/Fintype.card C ≤ 244/(2^255 : ℚ) ∧
      T₂.potential.queryBudget/Fintype.card C ≤ 459/(2^128 : ℚ)) := by
  have h₁ := S₁.withProfile_budgets_le Hash.profile geometry₁ sampling₁
    (by change 2^128 ≤ Nat.card F₁; simpa only [Nat.card_eq_fintype_card] using hfield₁)
  have h₂ := S₂.withProfile_budgets_le Signature.profile geometry₂ sampling₂
    (by change 2^255 ≤ Nat.card F₂; simpa only [Nat.card_eq_fintype_card] using hfield₂)
  exact ⟨h₁,h₂⟩

omit [Field Fmac] [DecidableEq Fmac] in
theorem coefficient_le (hfield₁ : 2^128 ≤ Fintype.card F₁) (hfield₂ : 2^255 ≤ Fintype.card F₂)
    (hmac : 2^128 ≤ Fintype.card Fmac) (hout₁ : out₁ ≤ 5) (hout₂ : out₂ ≤ 3) :
    let T₁ := S₁.withProfile Hash.profile geometry₁ sampling₁
    let T₂ := S₂.withProfile Signature.profile geometry₂ sampling₂
    TwoFieldFS.coefficient (Fmac := Fmac) circuit₁ I₁ circuit₂ I₂ T₁ T₂ ≤ coefficient := by
  intro T₁ T₂
  obtain ⟨h₁,h₂⟩ := terminal_rates circuit₁ I₁ circuit₂ I₂ S₁ S₂ geometry₁ geometry₂ sampling₁ sampling₂ hfield₁ hfield₂
  have hm := mac_rate_le hmac
  have hf₁ : (22 : ℚ)*max out₁ 2/Fintype.card F₁ ≤ 110/(2^128 : ℚ) := by
    have h := div_nat_le (by decide : 0 < 2^128) (by omega : 22*max out₁ 2 ≤ 110) hfield₁
    simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using h
  have hf₂ : (33 : ℚ)*max out₂ 2/Fintype.card F₂ ≤ 99/(2^255 : ℚ) := by
    have h := div_nat_le (by decide : 0 < 2^255) (by omega : 33*max out₂ 2 ≤ 99) hfield₂
    simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using h
  change max ((22 : ℚ)*33/Fintype.card Fmac)
    (max (max ((22 : ℚ)*max out₁ 2/Fintype.card F₁)
      (max (T₁.potential.challengeBudget/Fintype.card C) (T₁.potential.queryBudget/Fintype.card C)))
      (max ((33 : ℚ)*max out₂ 2/Fintype.card F₂)
        (max (T₂.potential.challengeBudget/Fintype.card C) (T₂.potential.queryBudget/Fintype.card C)))) ≤ _
  exact max_le (hm.trans (by norm_num [coefficient]))
    (max_le (max_le (hf₁.trans (by norm_num [coefficient]))
      (max_le (h₁.1.trans (by norm_num [coefficient])) (h₁.2.trans (by norm_num [coefficient]))))
      (max_le (hf₂.trans (by norm_num [coefficient]))
        (max_le (h₂.1.trans (by norm_num [coefficient])) (h₂.2.trans (by norm_num [coefficient])))))

omit [Field Fmac] [DecidableEq Fmac] in
theorem constant_le (hfield₁ : 2^128 ≤ Fintype.card F₁) (hfield₂ : 2^255 ≤ Fintype.card F₂)
    (hmac : 2^128 ≤ Fintype.card Fmac)
    (hfront₁ : out₁+circuit₁.sharpLayerBudget ≤ 655) (hfront₂ : out₂+circuit₂.sharpLayerBudget ≤ 552) :
    let T₁ := S₁.withProfile Hash.profile geometry₁ sampling₁
    let T₂ := S₂.withProfile Signature.profile geometry₂ sampling₂
    TwoFieldFS.constant (Fmac := Fmac) circuit₁ I₁ circuit₂ I₂ T₁ T₂ ≤ constant := by
  intro T₁ T₂
  obtain ⟨h₁,h₂⟩ := terminal_rates circuit₁ I₁ circuit₂ I₂ S₁ S₂ geometry₁ geometry₂ sampling₁ sampling₂ hfield₁ hfield₂
  have hm := mac_rate_le hmac
  have hf₁ : (22 : ℚ)*(out₁+circuit₁.sharpLayerBudget)/Fintype.card F₁ ≤ 14410/(2^128 : ℚ) := by
    have h := div_nat_le (by decide : 0 < 2^128)
      (by omega : 22*(out₁+circuit₁.sharpLayerBudget) ≤ 14410) hfield₁
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat] using h
  have hf₂ : (33 : ℚ)*(out₂+circuit₂.sharpLayerBudget)/Fintype.card F₂ ≤ 18216/(2^255 : ℚ) := by
    have h := div_nat_le (by decide : 0 < 2^255)
      (by omega : 33*(out₂+circuit₂.sharpLayerBudget) ≤ 18216) hfield₂
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat] using h
  change (22 : ℚ)*33/Fintype.card Fmac +
    ((22 : ℚ)*(out₁+circuit₁.sharpLayerBudget)/Fintype.card F₁ +
      T₁.potential.challengeBudget/Fintype.card C + T₁.potential.queryBudget/Fintype.card C) +
    ((33 : ℚ)*(out₂+circuit₂.sharpLayerBudget)/Fintype.card F₂ +
      T₂.potential.challengeBudget/Fintype.card C + T₂.potential.queryBudget/Fintype.card C) ≤ _
  calc
    _ ≤ 726/(2^128 : ℚ) + (14410/(2^128 : ℚ)+51/(2^128 : ℚ)+737/(2^128 : ℚ)) +
        (18216/(2^255 : ℚ)+244/(2^255 : ℚ)+459/(2^128 : ℚ)) :=
      add_le_add (add_le_add hm (add_le_add (add_le_add hf₁ h₁.1) h₁.2))
        (add_le_add (add_le_add hf₂ h₂.1) h₂.2)
    _ = constant := by norm_num [constant]

theorem error_le (hfield₁ : 2^128 ≤ Fintype.card F₁) (hfield₂ : 2^255 ≤ Fintype.card F₂)
    (hmac : 2^128 ≤ Fintype.card Fmac) (hout₁ : out₁ ≤ 5) (hout₂ : out₂ ≤ 3)
    (hfront₁ : out₁+circuit₁.sharpLayerBudget ≤ 655) (hfront₂ : out₂+circuit₂.sharpLayerBudget ≤ 552)
    (M : MacData C Fmac (Counting.tupleCounts I₁).Index (Counting.tupleCounts I₂).Index blocks)
    (N : ℕ) (proof : Proof Key C Public circuit₁ I₁ circuit₂ I₂) :
    let T₁ := S₁.withProfile Hash.profile geometry₁ sampling₁
    let T₂ := S₂.withProfile Signature.profile geometry₂ sampling₂
    (N*TwoFieldFS.maxBudget circuit₁ I₁ circuit₂ I₂ T₁ T₂ M +
      ∑ i, TwoFieldFS.slotBudget circuit₁ I₁ circuit₂ I₂ T₁ T₂ M i)/Fintype.card C ≤
        N*coefficient+constant := by
  intro T₁ T₂
  rw [TwoFieldFS.error_eq circuit₁ I₁ circuit₂ I₂ T₁ T₂ M N proof]
  exact add_le_add (mul_le_mul_of_nonneg_left
    (coefficient_le circuit₁ I₁ circuit₂ I₂ S₁ S₂ geometry₁ geometry₂ sampling₁ sampling₂
      hfield₁ hfield₂ hmac hout₁ hout₂) (Nat.cast_nonneg N))
    (constant_le circuit₁ I₁ circuit₂ I₂ S₁ S₂ geometry₁ geometry₂ sampling₁ sampling₂
      hfield₁ hfield₂ hmac hfront₁ hfront₂)

theorem constant_le_114 : constant ≤ 1/(2^114 : ℚ) := by norm_num [constant]
theorem coefficient_lt_117 : coefficient < 1/(2^117 : ℚ) := by norm_num [coefficient]

end LfzkV2.RuntimeCost
