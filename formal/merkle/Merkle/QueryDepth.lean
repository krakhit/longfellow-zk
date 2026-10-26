import Merkle.ExtractionROM

/-! A Merkle authentication path needs a chain of previously obtained
digests. Reusing a digest along that chain requires a query to hit a child
digest already specified by an earlier node input. This statement does not
assume indexed leaves or disjoint leaf/node encodings. -/

namespace Merkle.MH

open Finset RandomOracle
open scoped Classical

variable {Salt M D Enc : Type} [Inhabited D] [DecidableEq Enc]
variable (S : Scheme Salt M D Enc) (dec : RoleDecoders S.toCodec)

/-- Every queried child digest was obtained before its parent's hash input.
The complementary event is a predictable-digest hit, including self loops. -/
def ChildrenEarlier (seen : List Enc) : Prop :=
  ∀ parent ∈ seen, ∀ child ∈ seen, ∀ lr : D × D,
    dec.nodeDec parent = some lr →
    (S.H child = lr.1 ∨ S.H child = lr.2) →
    seen.idxOf child < seen.idxOf parent

private def pathQuery (n : ℕ) (I : Finset (Fin n)) (a : Fin n → M)
    (pf : Opening n I Salt D) (i : Fin n) (hi : i ∈ I) (v : ℕ) : Enc :=
  if v = n+i.val then S.leafEnc (pf.nonce ⟨i,hi⟩,a i)
  else S.nodeEnc (checkValues S n I a pf (2*v),checkValues S n I a pf (2*v+1))

private theorem internal_of_path_ne_leaf {n : ℕ} (i : Fin n) (v : ℕ)
    (hv : v ∈ Heap.pathOf n i) (hne : v ≠ n+i.val) : v < n := by
  obtain ⟨_,k,hk⟩ := Heap.mem_pathOf.mp hv
  have hkpos : 0 < k := by
    by_contra h
    have hk0 : k = 0 := by omega
    simp only [hk0,pow_zero,Nat.div_one] at hk
    exact hne hk
  have hp : 2 ≤ 2^k := Nat.le_self_pow (by omega) 2
  have hmul : v*2^k ≤ n+i.val := by
    rw [hk]
    exact Nat.div_mul_le_self _ _
  have hil := i.isLt
  nlinarith

private theorem pathQuery_spec (n : ℕ) (I : Finset (Fin n)) (a : Fin n → M)
    (pf : Opening n I Salt D) (i : Fin n) (hi : i ∈ I) (v : ℕ)
    (hv : v ∈ Heap.pathOf n i) :
    pathQuery S n I a pf i hi v ∈ checkTraceQueries S n I a pf ∧
      S.H (pathQuery S n I a pf i hi v) = checkValues S n I a pf v := by
  by_cases he : v = n+i.val
  · subst v
    simp only [pathQuery]
    constructor
    · apply mem_union_left
      exact mem_image.mpr ⟨⟨i,hi⟩,mem_attach I ⟨i,hi⟩,rfl⟩
    · exact (checkValues_leaf S n I a pf i hi).symm
  · have hn := internal_of_path_ne_leaf i v hv he
    have hpos := (Heap.mem_pathOf.mp hv).1
    have hpath := Heap.mem_pathSet.mpr ⟨i,hi,hv⟩
    simp only [pathQuery,if_neg he]
    constructor
    · apply mem_union_right
      exact mem_image.mpr ⟨v,mem_filter.mpr ⟨hpath,hpos,hn⟩,rfl⟩
    · exact (checkValues_node S n I a pf v ⟨hpos,hn,hpath⟩).symm

/-- Any opened leaf has strictly smaller depth than the number of distinct
queries explaining its authentication path, unless a predictable child
digest was hit. No bound on the number of distinct leaf values is needed. -/
theorem path_depth_lt_seen_length
    (n : ℕ) (I : Finset (Fin n)) (a : Fin n → M) (pf : Opening n I Salt D)
    (seen : List Enc) (hbefore : ChildrenEarlier S dec seen)
    (hqueries : ∀ q ∈ checkTraceQueries S n I a pf, q ∈ seen)
    (i : Fin n) (hi : i ∈ I) :
    Nat.log2 (n+i.val) < seen.length := by
  let q := pathQuery S n I a pf i hi
  have hmem v (hv : v ∈ Heap.pathOf n i) : q v ∈ seen :=
    hqueries _ (pathQuery_spec S n I a pf i hi v hv).1
  have hbound (v : ℕ) (hv : v ∈ Heap.pathOf n i) :
      seen.idxOf (q v) + Nat.log2 v ≤ seen.idxOf (q 1) := by
    induction v using Nat.strongRecOn with
    | ind v ih =>
      have hvpos := (Heap.mem_pathOf.mp hv).1
      by_cases hv1 : v = 1
      · subst v
        have hlog : Nat.log2 1 = 0 :=
          (Nat.log2_eq_iff (by decide)).mpr ⟨by norm_num,by norm_num⟩
        simp only [hlog,Nat.add_zero,le_refl]
      · have hv2 : 2 ≤ v := by omega
        have hp := Heap.parent_mem_pathOf hv (by omega)
        have hplt : v/2 < v := Nat.div_lt_self (by omega) (by omega)
        have hpn : v/2 < n := by
          have hb := (mem_Icc.mp (Heap.pathOf_mem_nodes_iff hv)).2
          have hil := i.isLt
          omega
        have hpne : v/2 ≠ n+i.val := by omega
        have hdec : dec.nodeDec (q (v/2)) =
            some (checkValues S n I a pf (2*(v/2)),checkValues S n I a pf (2*(v/2)+1)) := by
          simp only [q,pathQuery,if_neg hpne]
          exact dec.node_roundTrip _
        have hchild : S.H (q v) = checkValues S n I a pf (2*(v/2)) ∨
            S.H (q v) = checkValues S n I a pf (2*(v/2)+1) := by
          rw [(pathQuery_spec S n I a pf i hi v hv).2]
          have he : v = 2*(v/2) ∨ v = 2*(v/2)+1 := by omega
          rcases he with he | he
          · exact Or.inl (congrArg (checkValues S n I a pf) he)
          · exact Or.inr (congrArg (checkValues S n I a pf) he)
        have hidx := hbefore _ (hmem _ hp) _ (hmem _ hv) _ hdec hchild
        have hb := ih (v/2) hplt hp
        have hlog : Nat.log2 v = Nat.log2 (v/2)+1 := by
          rw [Nat.log2_def]
          exact if_pos hv2
        omega
  have hb := hbound (n+i.val) (Heap.leaf_mem_pathOf n i)
  have hr := List.idxOf_lt_length_of_mem (hmem 1 (Heap.root_mem_pathOf n i))
  omega

theorem eight_le_seen_length
    (n : ℕ) (hn : 128 ≤ n) (I : Finset (Fin n)) (a : Fin n → M)
    (pf : Opening n I Salt D) (hI : I.Nonempty)
    (seen : List Enc) (hbefore : ChildrenEarlier S dec seen)
    (hqueries : ∀ q ∈ checkTraceQueries S n I a pf, q ∈ seen) : 8 ≤ seen.length := by
  obtain ⟨i,hi⟩ := hI
  have h := path_depth_lt_seen_length S dec n I a pf seen hbefore hqueries i hi
  have hlog : 7 ≤ Nat.log2 (n+i.val) :=
    (Nat.le_log2 (by omega : n+i.val ≠ 0)).mpr (by norm_num; omega)
  omega

end Merkle.MH
