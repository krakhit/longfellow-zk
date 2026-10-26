import LfzkV2.Program

/-! Public/private input binding, including zero padding to a coefficient cube. -/

namespace LfzkV2

open SumcheckV2 Classical

variable {F ι κ : Type} [Field F] [Fintype ι] [Fintype κ]

noncomputable def zeroExtend (index : ι ↪ κ) (values : ι → F) (j : κ) : F :=
  ∑ i, if index i = j then values i else 0

omit [Fintype κ] in
@[simp] theorem zeroExtend_apply (index : ι ↪ κ) (values : ι → F) (i : ι) :
    zeroExtend index values (index i) = values i := by
  simp [zeroExtend, index.injective.eq_iff]

omit [Fintype κ] in
theorem zeroExtend_outside (index : ι ↪ κ) (values : ι → F) (j : κ)
    (hout : ∀ i, index i ≠ j) : zeroExtend index values j = 0 := by
  simp [zeroExtend, hout]

theorem dot_zeroExtend (index : ι ↪ κ) (weights : κ → F) (values : ι → F) :
    dot weights (zeroExtend index values) = dot (weights ∘ index) values := by
  simp only [dot, zeroExtend, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_ite]

/-- A physical input vector contains exactly the public prefix and the committed
private suffix; every other position of the padded cube is zero. -/
noncomputable def circuitInputs {n nPublic nPrivate : ℕ} {Slot : Type}
    (index : (Fin nPublic ⊕ Fin nPrivate) ↪ Cube n)
    (publicInputs : Fin nPublic → F) (privateCoordinate : Fin nPrivate → Slot)
    (witness : Slot → F) : Cube n → F :=
  zeroExtend index (Sum.elim publicInputs (witness ∘ privateCoordinate))

theorem input_sum {n nPublic nPrivate : ℕ} {Slot : Type}
    (index : (Fin nPublic ⊕ Fin nPrivate) ↪ Cube n) (weights : Cube n → F)
    (publicInputs : Fin nPublic → F) (privateCoordinate : Fin nPrivate → Slot)
    (witness : Slot → F) :
    dot weights (circuitInputs index publicInputs privateCoordinate witness) =
      dot (Sum.elim (fun i => weights (index (.inl i))) (fun i => weights (index (.inr i))))
        (Sum.elim publicInputs (witness ∘ privateCoordinate)) := by
  rw [circuitInputs, dot_zeroExtend]
  congr 1
  funext i
  cases i <;> rfl

/-- The circuit-level reduction for the actual rows emitted by the V2 compiler. -/
theorem compiled_circuit_reduction {out input nPublic nPrivate : ℕ} {Pad Slot : Type}
    (circuit : Circuit F out input) (m : circuit.Messages Pad Slot) (point : Fin out → F)
    (index : (Fin nPublic ⊕ Fin nPrivate) ↪ Cube input)
    (publicInputs : Fin nPublic → F) (privateCoordinate : Fin nPrivate → Slot)
    (coordinate : Pad → Slot) (witness : Slot → F) (cs : Constraints Pad Slot F)
    (hbuild : buildConstraints (circuit.proof m) = some cs)
    (hproducts : ProductsHold cs coordinate witness)
    (hrows : RowsHold (compile cs coordinate privateCoordinate
      (fun i => circuit.inputWeights m (monomialWeights point) (index (.inl i))) publicInputs
      (fun i => circuit.inputWeights m (monomialWeights point) (index (.inr i)))) witness)
    (hfalse : ¬ circuit.Satisfies (circuitInputs index publicInputs privateCoordinate witness)) :
    OutputBad (circuit.eval (circuitInputs index publicInputs privateCoordinate witness)) point ∨
      AssertedBad (witness ∘ coordinate) 0
        (circuit.execution m (circuitInputs index publicInputs privateCoordinate witness)
          (monomialWeights point)) := by
  apply circuit.soundness_reduction m _ point (witness ∘ coordinate) hfalse
  rw [input_sum]
  exact (compiled_iff_clear (circuit.proof m) cs hbuild coordinate privateCoordinate
    _ publicInputs _ witness hproducts).mp hrows

end LfzkV2
