import MaskSum

namespace WildAnchor
open Finset WildExact

/-- Canonical cycle sizes, measured in anchor edges. -/
def OrderedCycles (m low : Nat) (cs : List Nat) :=
  cs.sum=m ∧ (∀ l∈cs,low≤l) ∧ cs.Pairwise (·≤·)

def cycleLists : Nat → Nat → Nat → List (List Nat)
  | 0,_,m => if m=0 then [[]] else []
  | fuel+1,low,m => if m=0 then [[]] else (List.range (m+1)).flatMap fun a =>
      if low≤a ∧ 0<a then (cycleLists fuel a (m-a)).map (a::·) else []

private theorem member_aux {cs : List Nat} {m low fuel : Nat} (lo : 0<low)
    (ord : OrderedCycles m low cs) (len : cs.length≤fuel) : cs∈cycleLists fuel low m := by
  induction cs generalizing fuel m low with
  | nil =>
    obtain ⟨rfl,_,_⟩ := ord
    cases fuel <;> simp [cycleLists]
  | cons a rest ih =>
    obtain ⟨sz,all,sort⟩ := ord
    have al := all a (by simp)
    have eq : a+rest.sum=m := sz
    obtain ⟨least,tail⟩ := List.pairwise_cons.mp sort
    cases fuel with
    | zero => simp at len
    | succ fuel =>
      simp only [cycleLists,if_neg (show m≠0 by omega),List.mem_flatMap]
      refine ⟨a,List.mem_range.mpr (by omega),?_⟩
      rw [if_pos ⟨al,by omega⟩]
      apply List.mem_map_of_mem
      apply ih (by omega : 0<a) ⟨by omega,least,tail⟩
      simpa using len

private theorem length_bound (cs : List Nat) (pos : ∀ x∈cs,0<x) : cs.length≤cs.sum := by
  induction cs with
  | nil => simp
  | cons a rest ih =>
    have al := pos a (by simp)
    have more := ih (fun x hx => pos x (by simp [hx]))
    simp only [List.length_cons,List.sum_cons]
    omega

theorem cycle_member {cs : List Nat} {m low : Nat} (lo : 0<low) (ord : OrderedCycles m low cs) :
    cs∈cycleLists m low m :=
  member_aux lo ord ((length_bound cs (fun x hx => lo.trans_le (ord.2.1 x hx))).trans_eq ord.1)

/-- The sum of the bills can use how often each cycle type actually occurs
in the coloring. -/
theorem template_sum {m n k t : Nat} (g : Coloring n k) (a : Fin k)
    (e : Point m ≃ Fin n) (cs : {c : Fin k // c≠a} → List Nat)
    (frame : InFrame g a e (fun c => cyclePerm m (cs c)))
    (tag : Point m → Fin t) (root : Point m) (weights : Nat × Nat → Nat)
    (table : ∀ i j : Fin (m+1),sideCharge tag (tag root) (i.val,j.val)=weights (i.val,j.val))
    (anchor : ∀ i : Sides t (tag root),∃ j,(groupSide tag i j).1≠(groupSide tag i j).2)
    (budget : (∑ c,quickBill m weights (cs c))<m.factorial*2^m) : Upper g (starCost tag) := by
  apply anchored_upper g a e _ frame tag root (groupSide tag) bits all_bits (all_groupSides tag root) anchor
  simp_rw [charge_table tag (tag root) _ weights table]
  simpa only [quickBill_eq,bill] using budget

end WildAnchor
