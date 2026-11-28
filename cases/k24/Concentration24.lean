import CutModel30
import Mathlib.Data.List.Range

namespace WildSieve.TwentyFour

/-- A population is stored from the largest internal edge count down to zero. -/
def internalPairs : List Nat → Nat
  | [] => 0
  | a::xs => xs.length*a+internalPairs xs

def populations : Nat → Nat → Nat → List (List Nat)
  | 0,c,e => if c=0 ∧ e=0 then [[]] else []
  | k+1,c,e => do
      let a ← List.range (c+1)
      guard (k*a≤e ∧ e-k*a≤(k-1)*(c-a))
      let rest ← populations k (c-a) (e-k*a)
      pure (a::rest)

private theorem edge_bound (l : List Nat) : internalPairs l≤(l.length-1)*l.sum := by
  induction l with
  | nil => simp [internalPairs]
  | cons a l ih =>
    simp only [internalPairs,List.length_cons,Nat.add_sub_cancel,List.sum_cons,Nat.mul_add]
    exact Nat.add_le_add_left (ih.trans (Nat.mul_le_mul_right _ (Nat.sub_le _ _))) _

theorem population_member (l : List Nat) : l∈populations l.length l.sum (internalPairs l) := by
  induction l with
  | nil => decide
  | cons a l ih =>
    have choice : a∈List.range (a+l.sum+1) := List.mem_range.mpr (by omega)
    have okay : l.length*a≤l.length*a+internalPairs l ∧
        (l.length*a+internalPairs l-l.length*a)≤(l.length-1)*(a+l.sum-a) := by
      simpa only [Nat.add_sub_cancel_left,true_and,Nat.le_add_right] using edge_bound l
    simp only [List.length_cons,List.sum_cons,internalPairs,populations,List.bind_eq_flatMap,
      List.mem_flatMap] at *
    refine ⟨a,choice,?_⟩
    simpa [guard,okay,edge_bound l] using ih

def coords (u : Nat) := (List.range (u/2+1)).drop 2

def features (u : Nat) : List (List Nat) :=
  [[]] ++ (coords u).map (fun i => [i]) ++ (coords u).flatMap (fun i =>
    ((coords u).filter (i≤·)).map (fun j => [i,j]))

def feature (h : List Nat) : List Nat → Nat
  | [] => 1
  | [i] => h[i]!
  | i::j::_ => h[i]!*(h[j]!-(if i=j then 1 else 0))

def sixes (h : List Nat) (offset : Nat) : Nat :=
  ((List.range h.length).map fun i => h[i]!*(i+offset).choose 3).sum

def maxPairs (u inside : Nat) := if u=12 then inside else min (20*inside) (inside*(inside-1))

def price (u b : Nat) : List ℚ :=
  if u=12 then [499276/125,0,-363109/1000,-708927/1000,-134869/100,-251849/100,0,0,0,0,0,
    172909/20000,172909/5000,172909/2500,28239/200,172909/5000,138327/1000,282391/1000,161077/1000,702973/1000,370841/500]
  else if b=255 then [1/50,0,0,0,0,0,0,0,91/5,132053/100] else [0,0,0,0,0,0,0,0,0,616]

def polynomial (u b : Nat) (h : List Nat) : ℚ :=
  (((price u b).zip (features u)).map fun z => z.1*(feature h z.2 : ℚ)).sum

def jobs := [(12,55),(9,255),(9,270)]

private theorem checked : jobs.all (fun (u,b) =>
    (populations (u/2+1) 23 (u.choose 2)).all (fun l =>
      decide ((maxPairs u (sixes l.reverse 0)*(sixes l.reverse (12-u)-b) : Nat)≤
        polynomial u b l.reverse)))=true := by native_decide

/-- Each quadratic upper bound holds for every integer color population. -/
theorem concentration (u b : Nat) (job : (u,b)∈jobs) (l : List Nat)
    (size : l.length=u/2+1) (colors : l.sum=23) (edges : internalPairs l=u.choose 2) :
    (maxPairs u (sixes l.reverse 0)*(sixes l.reverse (12-u)-b) : Nat)≤polynomial u b l.reverse := by
  have mem := population_member l
  rw [size,colors,edges] at mem
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp checked (u,b) job) l mem)

#print axioms concentration
end WildSieve.TwentyFour
