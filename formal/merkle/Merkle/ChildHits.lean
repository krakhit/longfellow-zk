import Merkle.QueryDepth

/-! A node input specifies its two child digests before its hash answer is
read. Guessing one of those digests in the same or a later fresh slot is
bounded by an ordinary predictable-target count. -/

namespace Merkle.MH

open Finset RandomOracle
open scoped Classical

variable {Salt M D Enc Out : Type} [Inhabited D] [DecidableEq Enc]
variable {budget TM : ℕ}
variable {codec : Codec Salt M D Enc} (dec : RoleDecoders codec)
variable (tree : Tree Enc D Out budget) (ht : budget ≤ TM)

private def childValue (point : Option Enc) (left : Bool) : D :=
  (point.bind dec.nodeDec).elim default (fun lr => if left then lr.1 else lr.2)

abbrev ChildHitIndex (budget : ℕ) := Fin budget × Fin budget × Bool

def childHitSlot (p : ChildHitIndex budget) : Fin TM := ⟨p.1.val,lt_of_lt_of_le p.1.isLt ht⟩

noncomputable def childHitTarget (p : ChildHitIndex budget) (tape : Fin TM → D) : D :=
  childValue dec ((lazyRun (Function.update tape (childHitSlot ht p) default)
    default tree []).2.1[p.2.1.val]?) p.2.2

theorem childHitTarget_off (p : ChildHitIndex budget) :
    HitTarget (childHitSlot ht p) (childHitTarget dec tree ht p) :=
  hitTarget_of_neutralize (childHitSlot ht p) default
    (fun tape => childValue dec ((lazyRun tape default tree []).2.1[p.2.1.val]?) p.2.2)

noncomputable def ChildHit (tape : Fin TM → D) : Prop :=
  HitFamily TM (univ : Finset (ChildHitIndex budget)) (childHitSlot ht)
    (childHitTarget dec tree ht) tape

theorem childHit_card_le [Fintype D] [DecidableEq D] :
    (univ.filter (ChildHit dec tree ht)).card ≤
      (2*budget*budget)*Fintype.card D^(TM-1) := by
  have h := answerTape_hitFamily_card_le TM (univ : Finset (ChildHitIndex budget))
    (childHitSlot ht) (childHitTarget dec tree ht) (fun p _ => childHitTarget_off dec tree ht p)
  simpa only [ChildHit,card_univ,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,
    Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using h

/-- Outside the child-guessing event, every child known to the prover was
queried strictly before its parent. `H` can be a larger execution's oracle,
provided it agrees with the prover's permanent answer slots. -/
theorem childrenEarlier_of_not_childHit
    (tape : Fin TM → D) (H : Enc → D)
    (hanswers : ∀ q ∈ (lazyRun tape default tree []).2.1,
      H q = tapeAt tape default ((lazyRun tape default tree []).2.1.idxOf q))
    (hno : ¬ ChildHit dec tree ht tape) :
    ChildrenEarlier (codec.withOracle H) dec (lazyRun tape default tree []).2.1 := by
  intro parent hp child hc lr hdec hans
  let seen := (lazyRun tape default tree []).2.1
  have hlen : seen.length ≤ budget := by
    simpa only [seen,List.length_nil,zero_add] using lazyRun_seen_length_le tape default tree []
  have hpi : seen.idxOf parent < budget :=
    (List.idxOf_lt_length_of_mem hp).trans_le hlen
  have hci : seen.idxOf child < budget :=
    (List.idxOf_lt_length_of_mem hc).trans_le hlen
  by_contra hn
  change ¬ seen.idxOf child < seen.idxOf parent at hn
  have hle : seen.idxOf parent ≤ seen.idxOf child := by omega
  let i : Fin TM := ⟨seen.idxOf child,lt_of_lt_of_le hci ht⟩
  have hsame : (lazyRun (Function.update tape i default) default tree []).2.1[seen.idxOf parent]? =
      some parent := by
    have he := lazyRun_seen_take_congr (Function.update tape i default) tape default
      (seen.idxOf parent) (by
        intro j hj
        apply Function.update_of_ne
        intro heq
        have hv := congrArg Fin.val heq
        change j.val = seen.idxOf child at hv
        omega) tree []
    rw [← List.getElem?_take_of_lt (by omega : seen.idxOf parent < seen.idxOf parent+1),he,
      List.getElem?_take_of_lt (by omega : seen.idxOf parent < seen.idxOf parent+1)]
    exact List.getElem?_idxOf hp
  have hval : tape i = H child := by
    rw [hanswers child hc,tapeAt,dif_pos i.isLt]
  apply hno
  rcases hans with hl | hr
  · refine ⟨(⟨seen.idxOf child,hci⟩,⟨seen.idxOf parent,hpi⟩,true),mem_univ _,?_⟩
    change tape i = childValue dec
      ((lazyRun (Function.update tape i default) default tree []).2.1[seen.idxOf parent]?) true
    rw [hsame]
    simp only [childValue,Option.bind_some,hdec,Option.elim_some,if_true]
    exact hval.trans hl
  · refine ⟨(⟨seen.idxOf child,hci⟩,⟨seen.idxOf parent,hpi⟩,false),mem_univ _,?_⟩
    change tape i = childValue dec
      ((lazyRun (Function.update tape i default) default tree []).2.1[seen.idxOf parent]?) false
    rw [hsame]
    simp only [childValue,Option.bind_some,hdec,Option.elim_some,Bool.false_eq_true,if_false]
    exact hval.trans hr

end Merkle.MH
