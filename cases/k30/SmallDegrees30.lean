import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace WildSieve.Thirty
open Finset

/-- For degree d, bound the excess degrees of its neighbors by their maximum
and by the total excess remaining after the central vertex is removed. -/
def degreeCost (edges support largest d : Nat) : ℤ :=
  (d-1 : Nat) * ((min (2*edges-support-(d-1)) (d*(largest-1)) : Nat) - (d : ℤ))

private def slope (e n m : Nat) : ℤ := if e=4 ∧ n=4 ∧ m=3 then 1 else 0
private def intercept (e n m : Nat) : ℤ :=
  ((List.range m).map fun j => degreeCost e n m (j+1) - slope e n m*(j+1)).foldl max (-1)

private def cubic (e : Nat) : ℤ := ((e : ℤ)-1)*(e-3)*(e-4)

private theorem small_table :
    ∀ e : Fin 8, ∀ n : Fin 11, ∀ m : Fin 8,
      1≤e.val → 1≤m.val → m.val<n.val → m.val≤e.val →
      n.val-1≤2*e.val-m.val → 2*e.val-m.val≤(n.val-1)*m.val →
      (∀ d : Fin 8, 1≤d.val → d.val≤m.val →
          degreeCost e n m d ≤ slope e n m*d.val + intercept e n m) ∧
      degreeCost e n m m + slope e n m*(2*e.val-m.val : Nat) +
        intercept e n m*(n.val-1 : Nat) ≤ cubic e := by native_decide

/-- The finite degree step for any conflict graph on at most ten nonisolated
vertices and at most seven edges. All hypotheses refer only to the degrees. -/
theorem small_degree_sum {α : Type} [DecidableEq α] (U : Finset α)
    (deg : α → Nat) (v : α) (hv : v∈U) (e : Nat)
    (positive : ∀ x∈U, 1≤deg x)
    (largest : ∀ x∈U, deg x≤deg v)
    (degree_cap : deg v<U.card) (edges_cap : deg v≤e)
    (small : 1≤e ∧ e≤7) (order : U.card≤10)
    (handshake : ∑ x∈U,deg x=2*e) :
    ∑ x∈U,degreeCost e U.card (deg v) (deg x) ≤ cubic e := by
  let T := U.erase v
  have tc : T.card=U.card-1 := card_erase_of_mem hv
  have ds : (∑ x∈T,deg x)+deg v=2*e := (sum_erase_add _ _ hv).trans handshake
  have lo : T.card≤∑ x∈T,deg x := by
    simpa using sum_le_sum (s:=T) (fun x hx => positive x (mem_of_mem_erase hx))
  have hi : (∑ x∈T,deg x)≤T.card*deg v := by
    simpa using sum_le_sum (s:=T) (fun x hx => largest x (mem_of_mem_erase hx))
  have left : (∑ x∈T,deg x)=2*e-deg v := by omega
  rw [tc,left] at lo hi
  obtain ⟨per,cap⟩ := small_table ⟨e,by omega⟩ ⟨U.card,by omega⟩
    ⟨deg v,by omega⟩ small.1 (positive v hv) degree_cap edges_cap lo hi
  have each (x : α) (hx : x∈T) : degreeCost e U.card (deg v) (deg x) ≤
      slope e U.card (deg v)*(deg x : ℤ)+intercept e U.card (deg v) := per
    ⟨deg x,by have := largest x (mem_of_mem_erase hx); omega⟩
    (positive x (mem_of_mem_erase hx)) (largest x (mem_of_mem_erase hx))
  have rows := sum_le_sum each
  simp only [sum_add_distrib,←mul_sum,sum_const,nsmul_eq_mul,←Nat.cast_sum] at rows
  rw [left,tc] at rows
  have split := sum_erase_add U (fun x => degreeCost e U.card (deg v) (deg x)) hv
  change (∑ x∈T,degreeCost e U.card (deg v) (deg x))+_ = _ at split
  dsimp only at cap rows
  rw [←split]
  linarith

#print axioms small_degree_sum

end WildSieve.Thirty
