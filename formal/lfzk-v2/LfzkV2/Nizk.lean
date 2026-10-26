import LfzkV2.FiatShamir
import LfzkV2.Backend

/-!
# Composed V2 verifier and Fiat--Shamir reduction

`Reconstruction` contains only the public transcript reconstruction. Its rows
are the proved compiler's output, and its weights are computed from the trusted
circuit. The frontend theorem proves soundness for a fixed commitment candidate
family and explicit prefix replay. The composition theorem adds the backend's
acceptance-without-extraction probability; it does not assert that this term is
zero or instantiate an unproved numerical backend certificate.
-/

namespace LfzkV2

open SumcheckV2 Classical Finset
attribute [local instance 10000] Classical.propDecidable

variable {F Pad Slot : Type} [Field F]

structure Reconstruction {out input : ℕ} (circuit : Circuit F out input) (Pad Slot : Type) where
  messages : circuit.Messages Pad Slot
  point : Fin out → F
  constraints : Constraints Pad Slot F
  built : buildConstraints (circuit.proof messages) = some constraints

namespace Reconstruction

variable {out input nPublic nPrivate : ℕ} {circuit : Circuit F out input}
variable (view : Reconstruction circuit Pad Slot)
variable (index : (Fin nPublic ⊕ Fin nPrivate) ↪ Cube input)
variable (publicInputs : Fin nPublic → F) (privateCoordinate : Fin nPrivate → Slot)
variable (coordinate : Pad → Slot)

noncomputable def rows : List (LinearRow Slot F) :=
  compile view.constraints coordinate privateCoordinate
    (fun i => circuit.inputWeights view.messages (monomialWeights view.point) (index (.inl i)))
    publicInputs
    (fun i => circuit.inputWeights view.messages (monomialWeights view.point) (index (.inr i)))

def Accepts (witness : Slot → F) : Prop :=
  ProductsHold view.constraints coordinate witness ∧
    RowsHold (view.rows index publicInputs privateCoordinate coordinate) witness

noncomputable def tests (witness : Slot → F) : Tests F :=
  circuit.tests view.messages (circuitInputs index publicInputs privateCoordinate witness)
    view.point (witness ∘ coordinate)

theorem tests_valid (witness : Slot → F) :
    (view.tests index publicInputs privateCoordinate coordinate witness).Valid :=
  circuit.tests_valid view.messages (circuitInputs index publicInputs privateCoordinate witness)
    view.point (witness ∘ coordinate)

/-- The actual Polygero statement produced by this reconstruction. -/
noncomputable def backendStatement [Fintype F] [DecidableEq F]
    (I : RecursivePolygero.Instance F)
    (primary : Slot → Fin I.nw × Fin I.q)
    (product : Fin view.constraints.layers.length → Fin I.nq × Fin I.q)
    (eqns : I.Equations ≃ Backend.Equation
      (view.rows index publicInputs privateCoordinate coordinate).length view.constraints.layers.length) :
    I.layer.Statement :=
  Backend.statement (Backend.rows (view.rows index publicInputs privateCoordinate coordinate)
    view.constraints coordinate primary product ∘ eqns)

/-- Extraction validity for the actual compiled circuit statement. The row decoder
supplies both the affine equations and the products required by `Accepts`. -/
theorem decoded_accepts [Fintype F] [DecidableEq F]
    (I : RecursivePolygero.Instance F)
    (primary : Slot → Fin I.nw × Fin I.q)
    (product : Fin view.constraints.layers.length → Fin I.nq × Fin I.q)
    (eqns : I.Equations ≃ Backend.Equation
      (view.rows index publicInputs privateCoordinate coordinate).length view.constraints.layers.length)
    (oracle : I.layer.Oracle) (coin : I.layer.Coin) (response : I.layer.Payload)
    (g : (RecursivePolygero.Counting.tupleCounts I).Index)
    (hdecode : RecursivePolygero.scanRecoverAt I
      (Backend.statement (Backend.rows (view.rows index publicInputs privateCoordinate coordinate)
        view.constraints coordinate primary product ∘ eqns)) oracle coin response = some g) :
    view.Accepts index publicInputs privateCoordinate coordinate
      (Backend.read ((RecursivePolygero.Counting.tupleCounts I).witness g) ∘
        Backend.linearAddress primary) := by
  have h := Backend.decoded_compiled I (view.rows index publicInputs privateCoordinate coordinate)
    view.constraints coordinate primary product eqns oracle coin response g hdecode
  exact ⟨h.2, h.1⟩

/-- Algebraic satisfaction of the compiled backend enforces the same
frontend rows and products, independently of how the witness was obtained. -/
theorem satisfies_accepts [Fintype F] [DecidableEq F]
    (I : RecursivePolygero.Instance F)
    (primary : Slot → Fin I.nw × Fin I.q)
    (product : Fin view.constraints.layers.length → Fin I.nq × Fin I.q)
    (eqns : I.Equations ≃ Backend.Equation
      (view.rows index publicInputs privateCoordinate coordinate).length view.constraints.layers.length)
    (core : I.layer.Witness)
    (hsat : I.layer.satisfies
      (view.backendStatement index publicInputs privateCoordinate coordinate I primary product eqns) core) :
    view.Accepts index publicInputs privateCoordinate coordinate (Backend.read core ∘ Backend.linearAddress primary) := by
  have hbase : (Backend.statement (Backend.rows
      (view.rows index publicInputs privateCoordinate coordinate) view.constraints coordinate primary product)).Satisfies core := by
    obtain ⟨hl,hp⟩ := (Backend.statement_satisfies_iff _ _).mp hsat
    exact (Backend.statement_satisfies_iff _ _).mpr ⟨fun e => by simpa using hl (eqns.symm e),hp⟩
  have h := Backend.satisfies_compiled (view.rows index publicInputs privateCoordinate coordinate)
    view.constraints coordinate primary product core hbase
  exact ⟨h.2,h.1⟩

theorem accepts_false (witness : Slot → F)
    (hfalse : ∀ privateInputs : Fin nPrivate → F,
      ¬ circuit.Satisfies (zeroExtend index (Sum.elim publicInputs privateInputs)))
    (haccept : view.Accepts index publicInputs privateCoordinate coordinate witness) :
    (view.tests index publicInputs privateCoordinate coordinate witness).Bad := by
  rcases compiled_circuit_reduction circuit view.messages view.point index publicInputs
    privateCoordinate coordinate witness view.constraints view.built haccept.1 haccept.2
    (hfalse (witness ∘ privateCoordinate)) with houtput | htrace
  · exact (Tests.bad_append _ _).mpr (Or.inl ((outputTests_bad _ _).mpr houtput))
  · exact (Tests.bad_append _ _).mpr (Or.inr (traceTests_bad _ _ _ htrace))

end Reconstruction

namespace Nizk

variable {Q Out Key Context Candidate : Type}
variable [Fintype F] [DecidableEq F] [Fintype Q] [DecidableEq Q] [Fintype Candidate]
variable {N L out input nPublic nPrivate : ℕ}
variable (circuit : Circuit F out input)
variable (index : (Fin nPublic ⊕ Fin nPrivate) ↪ Cube input)
variable (publicInputs : Fin nPublic → F) (privateCoordinate : Fin nPrivate → Slot)
variable (coordinate : Pad → Slot)
variable (setup : FiatShamir.Setup F Q Out Key Context Candidate N L)
variable (view : (Q → F) → Reconstruction circuit Pad Slot)
variable (witness : (Q → F) → Candidate → Slot → F)

def ExtractedAccepts (H : Q → F) : Prop :=
  ∃ candidate, (view H).Accepts index publicInputs privateCoordinate coordinate (witness H candidate)

/-- The complete algebraic frontend against an adaptive FS adversary. The
remaining hypotheses identify the committed candidates and exact transcript
replay, not a claimed frontend soundness result. -/
theorem frontend_soundness
    (hfalse : ∀ privateInputs : Fin nPrivate → F,
      ¬ circuit.Satisfies (zeroExtend index (Sum.elim publicInputs privateInputs)))
    (hcover : ∀ H candidate, setup.Covers H candidate
      ((view H).tests index publicInputs privateCoordinate coordinate (witness H candidate)))
    (maxBudget : ℕ) (hmax : ∀ x, setup.budget x ≤ maxBudget)
    (slotBudget : Fin L → ℕ)
    (hslot : ∀ result i, setup.budget (setup.hashInput result i.val) ≤ slotBudget i) :
    ((univ.filter (ExtractedAccepts circuit index publicInputs privateCoordinate coordinate view witness)).card
        : ℚ) / (Fintype.card F : ℚ) ^ Fintype.card Q ≤
      (Fintype.card Candidate : ℚ) * (N * maxBudget + ∑ i, slotBudget i) / Fintype.card F := by
  apply setup.soundness_le maxBudget hmax slotBudget hslot
  intro H hH
  obtain ⟨candidate, haccept⟩ := hH
  exact ⟨candidate, _, hcover H candidate,
    (view H).accepts_false index publicInputs privateCoordinate coordinate
      (witness H candidate) hfalse haccept⟩

/-- Add the backend's extraction failure, which includes any required commitment
binding and backend FS reductions. No independence between the two events is used. -/
theorem composed_soundness
    (hfalse : ∀ privateInputs : Fin nPrivate → F,
      ¬ circuit.Satisfies (zeroExtend index (Sum.elim publicInputs privateInputs)))
    (hcover : ∀ H candidate, setup.Covers H candidate
      ((view H).tests index publicInputs privateCoordinate coordinate (witness H candidate)))
    (maxBudget : ℕ) (hmax : ∀ x, setup.budget x ≤ maxBudget)
    (slotBudget : Fin L → ℕ)
    (hslot : ∀ result i, setup.budget (setup.hashInput result i.val) ≤ slotBudget i)
    (accepts : (Q → F) → Prop) (extract : (Q → F) → Option Candidate)
    (extract_valid : ∀ H candidate, extract H = some candidate →
      (view H).Accepts index publicInputs privateCoordinate coordinate (witness H candidate))
    (backendError : ℚ)
    (hbackend : ((univ.filter fun H => accepts H ∧ extract H = none).card : ℚ) /
      (Fintype.card F : ℚ) ^ Fintype.card Q ≤ backendError) :
    ((univ.filter accepts).card : ℚ) / (Fintype.card F : ℚ) ^ Fintype.card Q ≤
      backendError +
        (Fintype.card Candidate : ℚ) * (N * maxBudget + ∑ i, slotBudget i) / Fintype.card F := by
  have hfront := frontend_soundness circuit index publicInputs privateCoordinate coordinate
    setup view witness hfalse hcover maxBudget hmax slotBudget hslot
  have hsub : univ.filter accepts ⊆
      (univ.filter fun H => accepts H ∧ extract H = none) ∪
        univ.filter (ExtractedAccepts circuit index publicInputs privateCoordinate coordinate view witness) := by
    intro H hH
    have ha := (mem_filter.mp hH).2
    cases he : extract H with
    | none => exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, ha, he⟩)
    | some candidate => exact mem_union_right _ (mem_filter.mpr
        ⟨mem_univ _, candidate, extract_valid H candidate he⟩)
  have hc := (card_le_card hsub).trans (card_union_le _ _)
  have hc' : ((univ.filter accepts).card : ℚ) ≤
      (univ.filter fun H => accepts H ∧ extract H = none).card +
        (univ.filter (ExtractedAccepts circuit index publicInputs privateCoordinate coordinate view witness)).card := by
    exact_mod_cast hc
  have hd := div_le_div_of_nonneg_right hc'
    (show (0 : ℚ) ≤ (Fintype.card F : ℚ) ^ Fintype.card Q by positivity)
  rw [add_div] at hd
  exact hd.trans (add_le_add hbackend hfront)

end Nizk

end LfzkV2
