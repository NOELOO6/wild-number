import CycleTemplates

namespace WildAnchor
open Finset

/-- Tail recursion keeps the finite check at 18 pairs within a small stack. -/
private def addDown (f : Nat → Nat) : Nat → Nat → Nat
  | 0,a => a
  | n+1,a => addDown f n (a+f n)

private theorem addDown_eq (f : Nat → Nat) (n a : Nat) :
    addDown f n a=a+∑ i∈range n,f i := by
  induction n generalizing a with
  | zero => simp [addDown]
  | succ n ih => rw [addDown,ih,sum_range_succ]; omega

private def entry (m : Nat) (prev : Array Nat) (mask : Nat) : Nat × Nat :=
  let count (v : Bool) := addDown (fun i =>
    if mask.testBit i == v && mask.testBit prev[i]! == v then 1 else 0) m 0
  (count false,count true)

def quickBill (m : Nat) (table : Nat × Nat → Nat) (cs : List Nat) :=
  let prev := Array.ofFn (fun i : Fin m => ((cyclePerm m cs).symm i).val)
  addDown (fun mask => table (entry m prev mask)) (2^m) 0

private theorem cached {m : Nat} (f : Fin m → Nat) (i : Fin m) :
    (Array.ofFn f)[i.val]! = f i := by
  have h : i.val < (Array.ofFn f).size := by simp
  simp only [getElem!_pos (c:=Array.ofFn f) (i:=i.val) h,Array.getElem_ofFn]

private theorem entry_eq {m : Nat} (p : Equiv.Perm (Fin m)) (b : Mask m) :
    entry m (Array.ofFn (fun i => (p.symm i).val)) b.val=key (row p (bits b)) := by
  apply Prod.ext <;> simp only [entry,addDown_eq,Nat.zero_add,key,width,Finset.sum_range]
  all_goals
    rw [← Nat.cast_id (Finset.card _), ← sum_boole (α:=Nat)]
    apply sum_congr rfl
    intro i _
    rw [cached]
    change _ = if kind (b.val.testBit i.val,b.val.testBit (p.symm i).val)=_ then 1 else 0
    cases b.val.testBit i.val <;> cases b.val.testBit (p.symm i).val <;> decide

theorem quickBill_eq (m : Nat) (table : Nat × Nat → Nat) (cs : List Nat) :
    quickBill m table cs=bill m table cs := by
  simp only [quickBill,addDown_eq,Nat.zero_add,Finset.sum_range,bill]
  apply sum_congr rfl
  intro i _
  rw [entry_eq (cyclePerm m cs) i]

end WildAnchor
