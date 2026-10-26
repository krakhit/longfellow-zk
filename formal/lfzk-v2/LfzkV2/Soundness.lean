import LfzkV2.Compiler
import SumcheckV2.Layer

/-!
# Composing V2 layer reductions

Each model supplies the effective tensor, its input-wire table, and the sampled
left point. `ConsistentChain` states the boundary between adjacent circuit
layers: the reweighted true input sum of one layer is the true incoming sum of
the next. This file proves propagation through the entire compiled constraint
system. `Program` constructs the circuit invariant, and `AssertedSoundness`
extends this reduction with initial output and intermediate assertion tests.
-/

namespace LfzkV2

open SumcheckV2

variable {F Pad Slot : Type} [Field F]

structure LayerModel (F : Type) where
  logSize : ℕ
  kernel : Cube logSize → Cube logSize → F
  wires : Cube logSize → F
  point : Fin logSize → F

namespace LayerModel

def truth (m : LayerModel F) : F := dot (bindRight m.kernel m.wires) m.wires

def nextTruth (m : LayerModel F) (alpha : F) : F :=
  dot (nextWeights m.kernel (monomialWeights m.point) alpha) m.wires

def Matches (m : LayerModel F) (t : LayerTranscript Pad Slot F) : Prop :=
  t.challenges = List.ofFn m.point

def Bad (m : LayerModel F) (t : LayerTranscript Pad Slot F) (pads : Pad → F)
    (claim : F) : Prop :=
  multi_round_bad_event claim (truePolys (bindRight m.kernel m.wires) m.wires m.point)
      (t.clearRounds pads) t.challenges ∨
    BadCombineEvent (evaluate m.wires m.point) (evaluate (bindRight m.kernel m.wires) m.point)
      (t.clearA pads) (t.clearB pads) t.alpha

theorem reduction (m : LayerModel F) (t : LayerTranscript Pad Slot F) (pads : Pad → F)
    (claim : F) (hshape : m.Matches t) (hfalse : claim ≠ m.truth)
    (hterminal : verify_multi_round claim (t.clearRounds pads) t.challenges =
      some (t.clearA pads * t.clearB pads))
    (hnext : t.clearA pads + t.alpha * t.clearB pads = m.nextTruth t.alpha) :
    m.Bad t pads claim := by
  unfold Bad
  rw [hshape] at hterminal ⊢
  exact layer_reduction m.kernel m.wires m.point claim (t.clearA pads) (t.clearB pads)
    t.alpha (t.clearRounds pads) hfalse hterminal hnext

/-- These are message-value equations, not an assumption that the verifier accepts. -/
def Honest (m : LayerModel F) (t : LayerTranscript Pad Slot F) (pads : Pad → F) : Prop :=
  t.clearRounds pads = honestMessages (bindRight m.kernel m.wires) m.wires m.point ∧
    t.clearA pads = evaluate m.wires m.point ∧
    t.clearB pads = evaluate (bindRight m.kernel m.wires) m.point

theorem completeness (m : LayerModel F) (t : LayerTranscript Pad Slot F) (pads : Pad → F)
    (hshape : m.Matches t) (hhonest : m.Honest t pads) :
    verify_multi_round m.truth (t.clearRounds pads) t.challenges =
        some (t.clearA pads * t.clearB pads) ∧
      t.clearA pads + t.alpha * t.clearB pads = m.nextTruth t.alpha := by
  rcases hhonest with ⟨hrounds, hA, hB⟩
  rw [hrounds, hA, hB, hshape]
  exact layer_completeness m.kernel m.wires m.point t.alpha

end LayerModel

abbrev Trace (Pad Slot F : Type) := List (LayerTranscript Pad Slot F × LayerModel F)

def transcripts (trace : Trace Pad Slot F) : List (LayerTranscript Pad Slot F) :=
  trace.map Prod.fst

def ConsistentChain (truth : F) : Trace Pad Slot F → F → Prop
  | [], inputSum => truth = inputSum
  | (t, m) :: rest, inputSum =>
      m.Matches t ∧ truth = m.truth ∧ ConsistentChain (m.nextTruth t.alpha) rest inputSum

def ChainBad (pads : Pad → F) (claim : F) : Trace Pad Slot F → Prop
  | [] => False
  | (t, m) :: rest =>
      m.Bad t pads claim ∨ ChainBad pads (t.clearA pads + t.alpha * t.clearB pads) rest

/-- An accepted false incoming claim must recover at some round or final-claim combination. -/
theorem chain_reduction (trace : Trace Pad Slot F) (pads : Pad → F)
    (claim truth inputSum : F) (hconsistent : ConsistentChain truth trace inputSum)
    (haccept : ClearAccepts pads claim (transcripts trace) inputSum) (hfalse : claim ≠ truth) :
    ChainBad pads claim trace := by
  induction trace generalizing claim truth with
  | nil => exact (hfalse (haccept.trans hconsistent.symm)).elim
  | cons entry rest ih =>
      rcases entry with ⟨t, m⟩
      rcases hconsistent with ⟨hshape, htruth, hrest⟩
      rcases haccept with ⟨hterminal, htail⟩
      by_cases hnext : t.clearA pads + t.alpha * t.clearB pads = m.nextTruth t.alpha
      · exact Or.inl (m.reduction t pads claim hshape (htruth ▸ hfalse) hterminal hnext)
      · exact Or.inr (ih _ _ hrest htail hnext)

/-- Honest round and terminal messages satisfy the entire clear verifier. -/
theorem chain_completeness (trace : Trace Pad Slot F) (pads : Pad → F) (truth inputSum : F)
    (hconsistent : ConsistentChain truth trace inputSum)
    (hhonest : ∀ entry ∈ trace, entry.2.Honest entry.1 pads) :
    ClearAccepts pads truth (transcripts trace) inputSum := by
  induction trace generalizing truth with
  | nil => exact hconsistent
  | cons entry rest ih =>
      rcases entry with ⟨t, m⟩
      rcases hconsistent with ⟨hshape, htruth, hrest⟩
      have hlayer := m.completeness t pads hshape (hhonest (t, m) List.mem_cons_self)
      constructor
      · simpa only [htruth] using hlayer.1
      · rw [hlayer.2]
        exact ih _ hrest (fun entry h => hhonest entry (List.mem_cons_of_mem _ h))

/-- The compiler preserves the whole-chain soundness reduction. This is deterministic;
the probability of the resulting bad events needs a prefix-adaptive challenge model. -/
theorem compiled_reduction {nPublic nPrivate : ℕ}
    (trace : Trace Pad Slot F) (cs : Constraints Pad Slot F)
    (hbuild : buildConstraints (transcripts trace) = some cs)
    (coordinate : Pad → Slot) (privateCoordinate : Fin nPrivate → Slot)
    (publicWeights publicInputs : Fin nPublic → F) (privateWeights : Fin nPrivate → F)
    (witness : Slot → F) (truth : F)
    (hproducts : ProductsHold cs coordinate witness)
    (hrows : RowsHold
      (compile cs coordinate privateCoordinate publicWeights publicInputs privateWeights) witness)
    (hconsistent : ConsistentChain truth trace
      (dot (Sum.elim publicWeights privateWeights)
        (Sum.elim publicInputs (witness ∘ privateCoordinate))))
    (hfalse : (0 : F) ≠ truth) :
    ChainBad (witness ∘ coordinate) 0 trace := by
  apply chain_reduction trace (witness ∘ coordinate) 0 truth _ hconsistent
  · exact (compiled_iff_clear (transcripts trace) cs hbuild coordinate privateCoordinate
      publicWeights publicInputs privateWeights witness hproducts).mp hrows
  · exact hfalse

end LfzkV2
