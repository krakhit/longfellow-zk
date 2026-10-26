import polygero.Local.Systems
import polygero.Local.Parameters
import polygero.Algebra.ExtendedGap

/-! Complete response uniqueness at a fixed reduced system, including proper
systems. The defect budget controls the arithmetic response as well as the
primary response. -/

noncomputable section
namespace RecursivePolygero.ProfileAnalysis
open Polynomial Finset Codes LigeroFamily Local Local.Polygero
open PolynomialClosure Shift MultiplicativeCode
open LigeroFamily.PolynomialDirect (primaryCode)
open scoped Classical
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
set_option maxHeartbeats 1000000

private def basePolynomial (I : Instance F) (row : EvaluationRow F I.r I.w I.n)
    (hrow : row ∈ ReedSolomon.evaluationSpace I.domain (I.r+I.w)) : DegreeLT F (I.r+I.w+1) :=
  ⟨Classical.choose ((ReedSolomon.mem_evaluationSpace I.domain).mp hrow),
    degreeLT_mono (by omega)
      (Classical.choose_spec ((ReedSolomon.mem_evaluationSpace I.domain).mp hrow)).1⟩

omit [Fintype F] [DecidableEq F] in
private theorem basePolynomial_eval (I : Instance F) (row : EvaluationRow F I.r I.w I.n)
    (hrow : row ∈ ReedSolomon.evaluationSpace I.domain (I.r+I.w)) (j : Fin I.n) :
    (basePolynomial I row hrow : F[X]).eval (I.domain.point (codePosition j)) = row (codePosition j) :=
  ((Classical.choose_spec ((ReedSolomon.mem_evaluationSpace I.domain).mp hrow)).2 _).symm

def arithmeticCoefficient (I : Instance F) (σ : I.layer.Statement)
    (α : I.Equations → F) (row : BatchedRow I.nw I.nq) : DegreeLT F (I.r+I.w+1) :=
  let hk : I.r+I.w ≤ I.n := by have := I.primary_le; omega
  let C := ReedSolomon.multiplicativeCode I.domain hk
  match row with
  | .inl ⟨block,i⟩ => basePolynomial I
      (DirectVerifier.coefficientRow C I.layout σ α block i) (C.encode_mem _ _)
  | .inr .vCoefficient => ⟨ReedSolomon.vanishingPolynomial I.domain, mem_degreeLT.mpr
      ((degree_le_natDegree).trans_lt (by
        rw [ReedSolomon.vanishingPolynomial_natDegree]
        exact_mod_cast Nat.lt_succ_self (I.r+I.w)))⟩
  | .inr .zRCoefficient => basePolynomial I C.zR C.zR_mem

theorem arithmeticCoefficient_eval (I : Instance F) (σ : I.layer.Statement)
    (α : I.Equations → F) (W : I.layer.Oracle) (j : Fin I.n) :
    (∑ i, (arithmeticCoefficient I σ α (rowEquiv I.nw I.nq i) : F[X]).eval
      (I.domain.point (codePosition j)) * oracleWords W.ordinary i j) =
      linearPointwise I.domain (by have := I.primary_le; omega) I.layout σ α j
        (fun i => oracleWords W.ordinary i j) := by
  change Oracle F I.nw I.nq I.n at W
  have hsum := (rowEquiv I.nw I.nq).sum_comp (fun row =>
    (arithmeticCoefficient I σ α row : F[X]).eval (I.domain.point (codePosition j)) *
      oracleWords W.ordinary ((rowEquiv I.nw I.nq).symm row) j)
  simp only [Equiv.symm_apply_apply] at hsum
  rw [hsum]
  simp [Fintype.sum_sum_type, Fintype.sum_sigma, arithmeticCoefficient, basePolynomial_eval,
    linearPointwise, PolynomialDirect.linearPointwise, extendRows, PolynomialDirect.coreIndex,
    PolynomialDirect.maskIndex, oracleWords, coreIndex, maskIndex, ReedSolomon.maskingBasis,
    ReedSolomon.vanishingRow, show (univ : Finset LinearConstraintMask) =
      {.vCoefficient,.zRCoefficient} from by decide, add_assoc]

theorem response_eq_of_assigned_system
    (I : Instance F) (p : ProfileParameters I) (σ : I.layer.Statement) (W : I.layer.Oracle)
    (d : systems I.domain I.primary_le W) (coin : I.layer.Coin)
    (first second : I.layer.Payload)
    (hfirst : (coin.2,first.primary) ∈ ConsistencyClosure.solutions
      (jointMap (primaryCode I.domain I.primary_le) (oracleWords W.ordinary)) W.proximityMask d.1)
    (hsecond : (coin.2,second.primary) ∈ ConsistencyClosure.solutions
      (jointMap (primaryCode I.domain I.primary_le) (oracleWords W.ordinary)) W.proximityMask d.1)
    (hlarge : ∀ payload ∈ ({first,second} : Finset _), p.largeSize ≤
      (goodColumns I.domain (by have := I.primary_le; omega) I.primary_le I.layout σ W coin payload).card)
    (hbudget : ∀ payload ∈ ({first,second} : Finset _),
      fixedConsistencyCodimension (primaryCode I.domain I.primary_le) (oracleWords W.ordinary) d.1 I.s +
        ((goodColumns I.domain (by have := I.primary_le; omega) I.primary_le I.layout σ W coin payload) \ d.1).card ≤ I.s) :
    first = second := by
  let C := primaryCode I.domain I.primary_le
  let δ := fixedConsistencyCodimension C (oracleWords W.ordinary) d.1 I.s
  let b := max (I.r+I.w) I.s
  have hgeom := geometry d
  have hsize : I.r+I.w+I.s ≤ d.1.card := by have := hgeom.core.large; omega
  have hδ : δ ≤ I.s := hgeom.core.low
  have hN : I.r+I.w+I.s+δ < d.1.card := hgeom.core.large
  have hrank : Module.finrank F (ProximityGap.polynomialSpace (C.node ∘ column d.1)
      (fun i => restrict d.1 (oracleWords W.ordinary i)) (I.r+I.w) I.s) = I.r+I.w+I.s+δ := by
    have h := joint_rank C (oracleWords W.ordinary) d.1 hsize
    rw [ConsistencyClosure.rank_eq_restriction,jointMap_range,
      ProximityGap.polynomialSpace_restrict] at h
    exact h
  have hprim : first.primary = second.primary := by
    apply Subtype.ext
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq d.1 C.node_injective.injOn
    · exact (mem_degreeLT.mp first.primary.2).trans_le (by exact_mod_cast hsize)
    · exact (mem_degreeLT.mp second.primary.2).trans_le (by exact_mod_cast hsize)
    · intro j hj
      have h1 := hfirst j hj
      have h2 := hsecond j hj
      change (first.primary : F[X]).eval (C.node j) - _ = _ at h1
      change (second.primary : F[X]).eval (C.node j) - _ = _ at h2
      exact sub_left_inj.mp (h1.trans h2.symm)
  let B : Fin (rowCount I.nw I.nq) → DegreeLT F (b+1) := fun i =>
    ⟨arithmeticCoefficient I σ coin.1 (rowEquiv I.nw I.nq i),
      degreeLT_mono (by dsimp [b]; omega) (arithmeticCoefficient I σ coin.1 (rowEquiv I.nw I.nq i)).2⟩
  let response : I.layer.Payload → DegreeLT F (I.r+I.w+b) := fun payload =>
    ⟨payload.arithmetic, degreeLT_mono (by dsimp [b]; omega) payload.arithmetic.2⟩
  have hcount (payload : I.layer.Payload) (hp : payload ∈ ({first,second} : Finset _)) :
      I.r+I.w+b+δ ≤ (univ.filter fun j => ProximityGap.batch (C.node ∘ column d.1)
        (fun i => restrict d.1 (oracleWords W.ordinary i)) B j =
          (response payload : F[X]).eval ((C.node ∘ column d.1) j)).card := by
    let G := goodColumns I.domain (by have := I.primary_le; omega) I.primary_le I.layout σ W coin payload
    have hg := hlarge payload hp
    have he := hbudget payload hp
    have hpart := card_sdiff_add_card_inter G d.1
    have hG : I.r+I.w+b+δ ≤ (G ∩ d.1).card := by
      change p.largeSize ≤ G.card at hg
      change δ+(G \ d.1).card ≤ I.s at he
      dsimp [b,ProfileParameters.largeSize,ProfileParameters.coreSize] at *
      omega
    have hsub : localColumns d.1 (G ∩ d.1) ⊆ (univ.filter fun j =>
        ProximityGap.batch (C.node ∘ column d.1)
          (fun i => restrict d.1 (oracleWords W.ordinary i)) B j =
            (response payload : F[X]).eval ((C.node ∘ column d.1) j)) := by
      intro j hj
      have hjG : column d.1 j ∈ G := (mem_inter.mp (mem_filter.mp hj).2).1
      have hv := ((mem_filter.mp hjG).2).2.1
      apply mem_filter.mpr
      refine ⟨mem_univ _,?_⟩
      change (∑ i, (arithmeticCoefficient I σ coin.1 (rowEquiv I.nw I.nq i) : F[X]).eval
        (I.domain.point (codePosition (column d.1 j))) * oracleWords W.ordinary i (column d.1 j)) = _
      rw [arithmeticCoefficient_eval]
      exact hv.symm
    have hc := card_le_card hsub
    rw [localColumns_card inter_subset_right] at hc
    exact hG.trans hc
  have ha := ExtendedGap.response_eq_of_large_agreement
    (C.node ∘ column d.1) (C.node_injective.comp (column_injective d.1))
    (fun i => restrict d.1 (oracleWords W.ordinary i)) (I.r+I.w) I.s δ b
    p.positive_degree hδ hN hrank (by dsimp [b]; omega) B (response first) (response second)
    (by
      convert! hcount first (by simp) using 1
      congr 1
      ext j
      simp only [mem_filter, mem_univ, true_and])
    (by
      convert! hcount second (by simp) using 1
      congr 1
      ext j
      simp only [mem_filter, mem_univ, true_and])
  have harith : first.arithmetic = second.arithmetic := Subtype.ext
    (congrArg (fun poly : DegreeLT F (I.r+I.w+b) => (poly : F[X])) ha)
  cases first
  cases second
  simp_all

end RecursivePolygero.ProfileAnalysis
