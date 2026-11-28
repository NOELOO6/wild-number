import EdgeWalk
import Lean.Data.Json
import Mathlib.Data.List.FinRange

namespace WildContractionExamples
open Lean WildDeletion EdgeWalk
set_option maxRecDepth 20000
set_option maxHeartbeats 0

structure Trial where
  n : Nat
  order : Array Nat
  cuts : Array (Nat × Nat)
  deriving Inhabited, FromJson

def trials : Array Trial := ((Json.parse (include_str "examples.json")).bind fromJson?).toOption.get!

def position (t : Trial) (x : Nat) := t.order.toList.idxOf x

def factorEdge (n c u v : Nat) : Bool :=
  u != v && (if u == n then v == c else if v == n then u == c else (u+v)%n == (2*c)%n)

def sameGroup (t : Trial) (x y : Nat) := position t x/3 == position t y/3

def wild (t : Trial) (x y : Nat) := x != y && sameGroup t x y &&
  (position t x%3 == 0 || position t y%3 == 0)

def geometry (t : Trial) : Bool :=
  let vs := List.range (t.n+1)
  let colors := List.range t.n
  let cost := vs.foldl (fun total u =>
    total+(vs.filter (fun v => u<v && wild t u v)).length) 0
  cost == 2*((t.n+1)/3) &&
    colors.all (fun c => vs.all fun u => (vs.filter (factorEdge t.n c u)).length == 1) &&
    vs.all (fun u => vs.all fun v => u == v || (colors.filter (fun c => factorEdge t.n c u v)).length == 1)

def evenEdges (t : Trial) (c : Fin t.n) : List (Edge (t.n+1)) :=
  (List.finRange (t.n+1)).flatMap fun x => ((List.finRange (t.n+1)).filter
    (fun y => x<y && (wild t x.val y.val || factorEdge t.n c.val x.val y.val))).map (x,·)

/-- More ordinary moves are allowed than a contraction needs: all edges within each
remaining block are available, as well as either orientation of the proposed extra edge. -/
def After (t : Trial) (c x y u v : Fin t.n) : Prop :=
  sameGroup t u.val v.val=true ∨ factorEdge t.n c.val u.val v.val=true ∨
    (u=x ∧ v=y) ∨ (u=y ∧ v=x)

def validCut (t : Trial) (cut : Nat × Nat) : Bool :=
  let s := cut.2
  cut.1<t.n && (List.range t.n).any s.testBit && (List.range t.n).any (fun x => !s.testBit x) &&
    (List.range t.n).all (fun u => (List.range t.n).all fun v =>
      !(sameGroup t u v || factorEdge t.n cut.1 u v) || s.testBit u == s.testBit v)

def tests (t : Trial) : Bool :=
  geometry t && t.n%6==5 && t.order.size==t.n+1 && (List.range (t.n+1)).all t.order.contains &&
  (List.finRange t.n).all (fun c => passes 0 (evenEdges t c)) &&
  (t.cuts.size==3 && t.cuts.toList.all (validCut t) &&
    (List.range 3).all (fun i => (List.range i).all fun j => t.cuts[i]!.2 &&& t.cuts[j]!.2 == 0) &&
    (List.finRange t.n).all (fun x => (List.finRange t.n).all fun y =>
      t.cuts.toList.any fun cut => cut.2.testBit x.val == cut.2.testBit y.val))

theorem catalogue : trials.toList.all tests=true := by native_decide
theorem orders : trials.map Trial.n=#[23,29,35,41,47,53,59,65,71] := by native_decide

private theorem obstructs (t : Trial) (cut : Nat × Nat) (hc : validCut t cut=true) (x y : Fin t.n)
    (same : cut.2.testBit x.val=cut.2.testBit y.val) :
    ∃ c : Fin t.n, ¬Connected (After t c x y) := by
  have h := Bool.and_eq_true_iff.mp hc
  have h1 := Bool.and_eq_true_iff.mp h.1
  have h2 := Bool.and_eq_true_iff.mp h1.1
  let c : Fin t.n := ⟨cut.1,of_decide_eq_true h2.1⟩
  obtain ⟨i,hi,inside⟩ := List.any_eq_true.mp h2.2
  obtain ⟨j,hj,outside⟩ := List.any_eq_true.mp h1.2
  let a : Fin t.n := ⟨i,List.mem_range.mp hi⟩
  let b : Fin t.n := ⟨j,List.mem_range.mp hj⟩
  have step {u v : Fin t.n} (e : After t c x y u v) : cut.2.testBit u.val=cut.2.testBit v.val := by
    have z := List.all_eq_true.mp (List.all_eq_true.mp h.2 u.val (List.mem_range.mpr u.isLt))
      v.val (List.mem_range.mpr v.isLt)
    rcases e with group|color|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · simpa [group] using z
    · change factorEdge t.n cut.1 u.val v.val=true at color
      simpa [color] using z
    · exact same
    · exact same.symm
  have invariant {u v : Fin t.n} (p : Walk (After t c x y) u v) :
      cut.2.testBit u.val=cut.2.testBit v.val := by
    induction p with
    | stay => rfl
    | step _ e ih => exact ih.trans (step e)
  refine ⟨c,fun conn => ?_⟩
  have eq := invariant (conn a b)
  change cut.2.testBit i=cut.2.testBit j at eq
  have no : cut.2.testBit j=false := by simpa using outside
  rw [inside,no] at eq
  contradiction

/-- Actual graph connectivity before deletion, and actual failure for every added edge after it. -/
theorem every_trial (t : Trial) (listed : t∈trials.toList) :
    (∀ c,Connected (Adj (evenEdges t c))) ∧ ∀ x y : Fin t.n,∃ c : Fin t.n,¬Connected (After t c x y) := by
  have good := List.all_eq_true.mp catalogue t listed
  have both := Bool.and_eq_true_iff.mp good
  have left := (Bool.and_eq_true_iff.mp both.1).2
  have right := Bool.and_eq_true_iff.mp both.2
  have valid := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp right.1).1).2
  constructor
  · exact fun c => connected_of_passes _ _ (List.all_eq_true.mp left c (List.mem_finRange c))
  · intro x y
    have h := List.all_eq_true.mp (List.all_eq_true.mp right.2 x (List.mem_finRange x)) y (List.mem_finRange y)
    obtain ⟨cut,hc,hs⟩ := List.any_eq_true.mp h
    exact obstructs t cut (List.all_eq_true.mp valid cut hc) x y (eq_of_beq hs)

#print axioms every_trial
end WildContractionExamples
