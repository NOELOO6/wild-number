import AnchoredGraph
import GraphLayouts
import Mathlib.Algebra.BigOperators.Fin
namespace WildAnchor
open Finset
variable {m t : Nat}
abbrev Mask (m : Nat) := Fin (2^m)
def bits (b : Mask m) (i : Fin m) := b.val.testBit i.val

theorem all_bits (f : Fin m → Bool) : ∃ b : Mask m,bits b=f := by
  let l := List.ofFn f
  let w := BitVec.ofBoolListLE l
  have len : l.length=m := List.length_ofFn
  refine ⟨⟨w.toNat,by rw [←len];exact w.isLt⟩,?_⟩
  funext i
  change (BitVec.ofBoolListLE l).getLsbD i.val = _
  rw [BitVec.getLsb_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by rw [len]; exact i.isLt)]
  simp [l]

abbrev Sides (t : Nat) (r : Fin t) := WildCuts.SideName (Fin t) r
def groupSide (tag : Point m → Fin t) {r : Fin t} (s : Sides t r) :=
  state (fun x => decide (tag x∈s.val))

theorem all_groupSides (tag : Point m → Fin t) (root : Point m) (h : Fin t → Bool)
    (off : h (tag root)=false) (on_ : ∃ j,h j=true) :
    ∃ i : Sides t (tag root),groupSide tag i=state (fun x => h (tag x)) := by
  classical
  let Z := univ.filter (fun j => h j=true)
  obtain ⟨j,hj⟩ := on_
  refine ⟨⟨Z,⟨j,mem_filter.mpr ⟨mem_univ _,hj⟩⟩,by simp [Z,off]⟩,?_⟩
  simp [groupSide,Z]

def key (s : State (Fin m)) := (width s 0,width s 2)
def mass (s : State (Fin m)) := (∏ j : Fin 3,(width s j).factorial)*2^(width s 0+width s 2)

private theorem widths (s : State (Fin m)) : width s 0+width s 1+width s 2=m := by
  have h := card_eq_sum_card_fiberwise (s:=(univ : Finset (Fin m))) (t:=(univ : Finset (Fin 3)))
    (f:=fun i => kind (s i)) (fun _ _ => mem_univ _)
  simpa [width,Fin.sum_univ_succ,Nat.add_assoc] using h.symm

private theorem by_key (s b : State (Fin m)) : price s b=if key s=key b then mass s else 0 := by
  have h : (∀ j,width s j=width b j) ↔ key s=key b := by
    constructor
    · intro a;exact Prod.ext (a 0) (a 2)
    · intro eq j
      have a := congrArg Prod.fst eq
      have d := congrArg Prod.snd eq
      change width s 0=width b 0 at a
      change width s 2=width b 2 at d
      have b1 := widths s
      have b2 := widths b
      rcases (show j=0 ∨ j=1 ∨ j=2 by omega) with rfl|rfl|rfl <;> omega
  simp only [price,mass,h]

def sideCharge (tag : Point m → Fin t) (r : Fin t) (key' : Nat × Nat) :=
  ∑ a : Sides t r, if key (groupSide tag a)=key' then mass (groupSide tag a) else 0

theorem charge_table (tag : Point m → Fin t) (r : Fin t) (next : Equiv.Perm (Fin m))
    (table : Nat × Nat → Nat)
    (check : ∀ i j : Fin (m+1),sideCharge tag r (i.val,j.val)=table (i.val,j.val)) :
    (∑ a : Sides t r,∑ b : Mask m,price (groupSide tag a) (row next (bits b))) =
      ∑ b : Mask m,table (key (row next (bits b))) := by
  rw [sum_comm]
  apply sum_congr rfl
  intro b _
  let s := row next (bits b)
  have sm (j : Fin 3) : width s j≤m := (card_le_card (filter_subset _ _)).trans_eq (by simp)
  simpa only [sideCharge,by_key,key] using check ⟨_,Nat.lt_succ_of_le (sm 0)⟩ ⟨_,Nat.lt_succ_of_le (sm 2)⟩
end WildAnchor
