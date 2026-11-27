import NearCharge
import UniversalLower

namespace WildCuts.OneExtra
open Finset EdgeWalk WildDeletion WildExact

def order (i : Nat) := 15+2*i
def regular (i : Nat) := order i/3-1
def template (i : Nat) : WildCuts.Blocks (Fin (order i)) (Fin (regular i+1)) where
  tag x := ⟨min (x.val/3) (regular i),by omega⟩
  rep g := ⟨3*g.val,by have := g.isLt; dsimp [regular,order] at *; omega⟩
  section_ g := by apply Fin.ext; dsimp; have := g.isLt; omega

def endPair (i : Nat) : Fin ((order i+1)/2) :=
  ⟨(order i+1)/2-1,by dsimp [order]; omega⟩

/-- Every test here has at most quadratically many entries. The cut sums
themselves are compressed using the theorem in NearCharge. -/
def passesOrder (i : Nat) := Id.run do
  let n := order i
  let t := regular i
  let b := template i
  let h := (n+1)/2
  return decide (∀ p,p≠Fin.last t → width b p=3) &&
    decide (∀ p,width (pairs n) p=if p=endPair i then 1 else 2) &&
    decide (Fintype.card (Line n)=n*(n/2)) &&
    decide (n*singleCutSum n t (h-1)<n.factorial*3) &&
    decide ((((List.finRange n).filter fun x => x != b.rep (b.tag x))).length=(2*n+2)/3)

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem checked : (List.range 34).all passesOrder=true := by decide

theorem placement_near (i : Nat) (small : i<34) (m : Fin (order i) → List (Edge (order i)))
    (complete : ∀ x y, x≠y → ∃ c,Adj (m c) x y)
    (proper : ∀ c x y z, Adj (m c) x y → Adj (m c) x z → y=z) :
    Solution m ((2*order i+2)/3+1) := by
  let n := order i
  let t := regular i
  let b := template i
  have check := List.all_eq_true.mp checked i (List.mem_range.mpr small)
  simp only [passesOrder,Id.run,pure,Bool.and_eq_true,decide_eq_true_eq] at check
  obtain ⟨⟨⟨⟨tr,d⟩,line⟩,num⟩,stars⟩ := check
  haveI : Nontrivial (Fin (order i)) := Fin.nontrivial_iff_two_le.mpr (by dsimp [order]; omega)
  apply graph_bound (k:=n/2) (base:=(2*n+2)/3) b (Fin.last t) m complete proper rfl line _ stars
  exact lt_of_le_of_lt (Nat.mul_le_mul_left n (compressed b (pairs n) tr (endPair i) d)) num

private noncomputable def colorList {n : Nat} (g : Coloring n n) (c : Fin n) :=
  ((univ : Finset (Fin n × Fin n)).filter (fun e => e.1<e.2 ∧ g.paint e.1 e.2=c)).toList

private theorem list_color {n : Nat} (g : Coloring n n) (c x y : Fin n) :
    Adj (colorList g c) x y ↔ x≠y ∧ g.paint x y=c := by
  simp only [Adj,colorList,Finset.mem_toList,mem_filter,mem_univ,true_and]
  rw [g.symm y x]
  constructor
  · rintro (⟨lt,h⟩|⟨lt,h⟩)
    · exact ⟨lt.ne,h⟩
    · exact ⟨lt.ne',h⟩
  · rintro ⟨ne,h⟩
    rcases lt_or_gt_of_ne ne with a|a
    · exact Or.inl ⟨a,h⟩
    · exact Or.inr ⟨a,h⟩

private theorem convert {n b : Nat} (g : Coloring n n) (h : Solution (colorList g) b) : Upper g b := by
  obtain ⟨w,_,legal,size,works⟩ := h
  refine ⟨w.toFinset,fun e he => legal e (List.mem_toFinset.mp he),w.toFinset_card_le.trans size,?_⟩
  intro c a z
  apply Walk.mapInto (E:=Adj (w++colorList g c)) (F:=Joined g w.toFinset c) id _ (works c a z)
  intro x y edge
  apply Walk.step (.stay x)
  rcases edge with e|e
  · rcases List.mem_append.mp e with l|r
    · exact Or.inl (Or.inl (List.mem_toFinset.mpr l))
    · exact Or.inr ((list_color g c x y).mp (Or.inl r))
  · rcases List.mem_append.mp e with l|r
    · exact Or.inl (Or.inr (List.mem_toFinset.mpr l))
    · exact Or.inr ((list_color g c x y).mp (Or.inr r))

/-- At all orders from 15 to 82, one extra wild edge above the conjectured
minimum always suffices, simultaneously for every color. -/
theorem one_extra_pair (n : Nat) (lo : 15≤n) (hi : n≤81) (odd : n%2=1) :
    (∀ g : Coloring n n, Upper g ((2*n+2)/3+1)) ∧
    (∀ g : Coloring (n+1) n, Upper g ((2*n+2)/3+1)) := by
  have upper (g : Coloring n n) : Upper g ((2*n+2)/3+1) := by
    obtain ⟨i,lt,rfl⟩ : ∃ i,i<34 ∧ n=order i := ⟨(n-15)/2,by omega,by dsimp [order]; omega⟩
    apply convert g (placement_near i lt (colorList g) ?_ ?_)
    · intro x y ne
      exact ⟨g.paint x y,(list_color _ _ _ _).mpr ⟨ne,rfl⟩⟩
    · intro c x y z xy xz
      obtain ⟨ny,ey⟩ := (list_color _ _ _ _).mp xy
      obtain ⟨nz,ez⟩ := (list_color _ _ _ _).mp xz
      exact g.proper x y z ny nz (ey.trans ez.symm)
  exact ⟨upper,even_upper upper⟩

#print axioms one_extra_pair
end WildCuts.OneExtra
