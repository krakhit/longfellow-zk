import LfzkV2.Backend
import LfzkV2.PolygeroZk

/-!
# Honest Polygero encoding of the actual V2 compiler rows

The compiler's ordinary coordinates and product copies satisfy the simulator
interface for every encoding prefix. Product-copy columns are embedded into
the shorter input-code witness positions. No arbitrary statement-validity or
coefficient-support premise is introduced at this boundary.
-/

namespace LfzkV2.BackendEncoding

open LigeroFamily MultiplicativeCode Backend

variable {F Pad Slot : Type} [Field F] {r w p n nw nq : ℕ}
variable (G : PolygeroZk.Geometry F r w p n)

def productMap {layers : ℕ} (positions : Fin layers → Fin nq × Fin p) :
    Fin layers → Fin nq × Fin w :=
  fun i => ((positions i).1, G.productSlots (positions i).2)

def productValue (messages : PolygeroCoreMasking.Messages F w p nw nq)
    (position : Fin nq × Fin p) : CopyKind → F
  | .left => messages.left position.1 position.2
  | .right => messages.right position.1 position.2
  | .product => messages.left position.1 position.2 * messages.right position.1 position.2

/-- Populate the ordinary vector and the two product-input copies, using the
same zero extension as the frontend's input encoding. -/
noncomputable def encodeMessages [Fintype Slot] (cs : Constraints Pad Slot F)
    (coordinate : Pad → Slot) (primary : Slot ↪ Fin nw × Fin w)
    (positions : Fin cs.layers.length ↪ Fin nq × Fin p) (values : Slot → F) :
    PolygeroCoreMasking.Messages F w p nw nq where
  ordinary row col := zeroExtend primary values (row,col)
  left row col := zeroExtend positions (fun i => values (coordinate (cs.layers.get i).padA)) (row,col)
  right row col := zeroExtend positions (fun i => values (coordinate (cs.layers.get i).padB)) (row,col)

theorem encodeMessages_primary [Fintype Slot] (cs : Constraints Pad Slot F)
    (coordinate : Pad → Slot) (primary : Slot ↪ Fin nw × Fin w)
    (positions : Fin cs.layers.length ↪ Fin nq × Fin p) (values : Slot → F) (slot : Slot) :
    (encodeMessages cs coordinate primary positions values).ordinary (primary slot).1 (primary slot).2 =
      values slot := zeroExtend_apply primary values slot

theorem encodeMessages_product [Fintype Slot] (cs : Constraints Pad Slot F)
    (coordinate : Pad → Slot) (primary : Slot ↪ Fin nw × Fin w)
    (positions : Fin cs.layers.length ↪ Fin nq × Fin p) (values : Slot → F)
    (hproducts : ProductsHold cs coordinate values) (i : Fin cs.layers.length) (kind : CopyKind) :
    productValue (encodeMessages cs coordinate primary positions values) (positions i) kind =
      values (kind.slot (cs.layers.get i) coordinate) := by
  have hl : (encodeMessages cs coordinate primary positions values).left (positions i).1 (positions i).2 =
      values (coordinate (cs.layers.get i).padA) := zeroExtend_apply positions _ i
  have hr : (encodeMessages cs coordinate primary positions values).right (positions i).1 (positions i).2 =
      values (coordinate (cs.layers.get i).padB) := zeroExtend_apply positions _ i
  cases kind with
  | left => exact hl
  | right => exact hr
  | product => exact (congrArg₂ (· * ·) hl hr).trans (hproducts (cs.layers.get i) (List.get_mem _ _)).symm

theorem read_primary (messages : PolygeroCoreMasking.Messages F w p nw nq)
    (tape : PolygeroCoreMasking.Tape F r nw nq) (primary : Slot → Fin nw × Fin w) (slot : Slot) :
    read (layoutCoreMessages (ConstraintLayout.identity w) (PolygeroZk.core G messages tape))
      (linearAddress primary slot) = messages.ordinary (primary slot).1 (primary slot).2 :=
  G.code.encode_witness _ _ _

theorem read_product (messages : PolygeroCoreMasking.Messages F w p nw nq)
    (tape : PolygeroCoreMasking.Tape F r nw nq) (position : Fin nq × Fin p) (kind : CopyKind) :
    read (layoutCoreMessages (ConstraintLayout.identity w) (PolygeroZk.core G messages tape))
      (productAddress (position.1, G.productSlots position.2) kind) = productValue messages position kind := by
  cases kind with
  | left => exact PolygeroCoreMasking.input_witness G.domain G.k_le_n G.productSlots _ _ _
  | right => exact PolygeroCoreMasking.input_witness G.domain G.k_le_n G.productSlots _ _ _
  | product =>
      change PolygeroCoreMasking.input G.domain G.k_le_n G.productSlots
          (tape.2.1 position.1) (messages.left position.1) (witnessPosition (G.productSlots position.2)) *
        PolygeroCoreMasking.input G.domain G.k_le_n G.productSlots
          (tape.2.2 position.1) (messages.right position.1) (witnessPosition (G.productSlots position.2)) = _
      rw [PolygeroCoreMasking.input_witness, PolygeroCoreMasking.input_witness]
      rfl

def Active (address : Address nw nq w) : Prop :=
  address.1 = .linear ∨ address.2.2 ∈ Set.range G.productSlots

private theorem coefficients_zero {ι : Type} (terms : List (ι × F)) (active : ι → Prop)
    (hterms : ∀ term ∈ terms, active term.1) (address : ι) (hout : ¬ active address) :
    Backend.coefficients terms address = 0 := by
  classical
  unfold Backend.coefficients
  apply List.sum_eq_zero
  intro value hvalue
  obtain ⟨term, hterm, rfl⟩ := List.mem_map.mp hvalue
  exact if_neg (show address ≠ term.1 by
    intro heq
    apply hout
    rw [heq]
    exact hterms term hterm)

theorem rows_active (linear : List (LinearRow Slot F)) (cs : Constraints Pad Slot F)
    (coordinate : Pad → Slot) (primary : Slot → Fin nw × Fin w)
    (positions : Fin cs.layers.length → Fin nq × Fin p)
    (equation : Equation linear.length cs.layers.length)
    (term : Address nw nq w × F)
    (hterm : term ∈ (Backend.rows linear cs coordinate primary (productMap G positions) equation).terms) :
    Active G term.1 := by
  cases equation with
  | inl i =>
      obtain ⟨original, _, heq⟩ := List.mem_map.mp hterm
      subst term
      exact Or.inl rfl
  | inr pair =>
      rcases pair with ⟨i,kind⟩
      change term ∈ [(_,1),(_,-1)] at hterm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hterm
      rcases hterm with rfl | rfl
      · cases kind <;> exact Or.inr ⟨(positions i).2,rfl⟩
      · exact Or.inl rfl

/-- Coefficient support follows from the compiler's concrete terms. -/
theorem rows_supported (linear : List (LinearRow Slot F)) (cs : Constraints Pad Slot F)
    (coordinate : Pad → Slot) (primary : Slot → Fin nw × Fin w)
    (positions : Fin cs.layers.length → Fin nq × Fin p)
    (equation : Equation linear.length cs.layers.length) (block : CoreBlock)
    (row : Fin (block.rowCount nw nq)) (col : Fin w)
    (hout : ¬ (block = .linear ∨ col ∈ Set.range G.productSlots)) :
    (Backend.statement (Backend.rows linear cs coordinate primary (productMap G positions))).coefficient
      equation block row col = 0 :=
  coefficients_zero _ (Active G) (rows_active G linear cs coordinate primary positions equation) _ hout

/-- Honest row placement supplies the exact interface used by the joint
Polygero simulator, for every ordinary and product-input random prefix. -/
theorem compatible (linear : List (LinearRow Slot F)) (cs : Constraints Pad Slot F)
    (coordinate : Pad → Slot) (primary : Slot → Fin nw × Fin w)
    (positions : Fin cs.layers.length → Fin nq × Fin p)
    (messages : PolygeroCoreMasking.Messages F w p nw nq) (values : Slot → F)
    (hrows : RowsHold linear values)
    (hprimary : ∀ slot, messages.ordinary (primary slot).1 (primary slot).2 = values slot)
    (hcopy : ∀ i kind, productValue messages (positions i) kind =
      values (kind.slot (cs.layers.get i) coordinate)) :
    PolygeroZk.Compatible G messages
      (Backend.statement (Backend.rows linear cs coordinate primary (productMap G positions))) := by
  refine ⟨rows_supported G linear cs coordinate primary positions, ?_⟩
  intro tape
  apply (Backend.statement_satisfies_iff _ _).2
  constructor
  · intro equation
    cases equation with
    | inl i =>
        change (Backend.remap (linear.get i) (linearAddress primary)).eval _ = 0
        rw [Backend.eval_remap]
        have hread : read
            (layoutCoreMessages (ConstraintLayout.identity w) (PolygeroZk.core G messages tape)) ∘
              linearAddress primary = values := by
          funext slot
          exact (read_primary G messages tape primary slot).trans (hprimary slot)
        rw [hread]
        exact hrows (linear.get i) (List.get_mem _ _)
    | inr pair =>
        rcases pair with ⟨i,kind⟩
        change (Backend.copyRow (cs.layers.get i) coordinate primary (productMap G positions i) kind).eval _ = 0
        rw [Backend.eval_copyRow]
        change read _ (productAddress ((positions i).1,G.productSlots (positions i).2) kind) - _ = 0
        rw [read_product, read_primary, hcopy, hprimary, sub_self]
  · intro row col
    exact PolygeroCoreMasking.encoding_product G.domain G.k_le_n G.productSlots
      messages tape row (witnessPosition col)

/-- The simulator compatibility hypotheses follow from satisfied compiler
rows and committed products for the explicitly constructed message tableau. -/
theorem compatible_encoded [Fintype Slot]
    (linear : List (LinearRow Slot F)) (cs : Constraints Pad Slot F)
    (coordinate : Pad → Slot) (primary : Slot ↪ Fin nw × Fin w)
    (positions : Fin cs.layers.length ↪ Fin nq × Fin p) (values : Slot → F)
    (hrows : RowsHold linear values) (hproducts : ProductsHold cs coordinate values) :
    PolygeroZk.Compatible G (encodeMessages cs coordinate primary positions values)
      (Backend.statement (Backend.rows linear cs coordinate primary (productMap G positions))) :=
  compatible G linear cs coordinate primary positions _ values hrows
    (encodeMessages_primary cs coordinate primary positions values)
    (encodeMessages_product cs coordinate primary positions values hproducts)

/-- The actual V2 affine compiler supplies those rows from its symbolic
constraints; no extra backend-satisfaction assumption is needed. -/
theorem compatible_compiled [Fintype Slot] {nPublic nPrivate : ℕ}
    (cs : Constraints Pad Slot F) (coordinate : Pad → Slot)
    (privateCoordinate : Fin nPrivate → Slot)
    (publicWeights publicInputs : Fin nPublic → F) (privateWeights : Fin nPrivate → F)
    (primary : Slot ↪ Fin nw × Fin w) (positions : Fin cs.layers.length ↪ Fin nq × Fin p)
    (values : Slot → F) (hproducts : ProductsHold cs coordinate values)
    (hholds : cs.Holds (values ∘ coordinate)
      (SumcheckV2.dot (Sum.elim publicWeights privateWeights)
        (Sum.elim publicInputs (values ∘ privateCoordinate)))) :
    PolygeroZk.Compatible G (encodeMessages cs coordinate primary positions values)
      (Backend.statement (Backend.rows
        (compile cs coordinate privateCoordinate publicWeights publicInputs privateWeights)
        cs coordinate primary (productMap G positions))) :=
  compatible_encoded G _ cs coordinate primary positions values
    ((compile_correct cs coordinate privateCoordinate publicWeights publicInputs privateWeights
      values hproducts).2 hholds) hproducts

end LfzkV2.BackendEncoding
