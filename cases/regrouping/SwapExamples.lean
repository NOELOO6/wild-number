import Periodic
import GraphSearch
namespace WildExact.Regroup
open WildDeletion EdgeWalk
set_option maxRecDepth 10000

private def swapPoints {n} (x y : Fin n) (g : List (List Nat)) :=
  g.map fun t => t.map fun v => if v=x.val then y.val else if v=y.val then x.val else v

private def colors {n} (g : Coloring n n) (c : Fin n) :=
  (List.finRange n).flatMap fun x => ((List.finRange n).filter (fun y => x<y && g.paint x y==c)).map (x,·)

def layoutEdges {n} [NeZero n] (g : Coloring n n) (t : List (List Nat)) (c : Fin n) := chains t ++ colors g c

def loses {n} [NeZero n] (es : List (Edge n)) :=
  let s := run es n 1
  ((List.finRange n).any (fun v => s.testBit v.val)) &&
  ((List.finRange n).any (fun v => !s.testBit v.val)) &&
  es.all (fun e => s.testBit e.1.val == s.testBit e.2.val)

theorem lost {n} [NeZero n] {es : List (Edge n)} (h : loses es=true) : ¬ Connected (Adj es) := by
  let s := run es n 1
  obtain ⟨points,closed⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨yes,no⟩ := Bool.and_eq_true_iff.mp points
  obtain ⟨x,_,hx⟩ := List.any_eq_true.mp yes
  obtain ⟨y,_,hy⟩ := List.any_eq_true.mp no
  have same {i j : Fin n} (p : Walk (Adj es) i j) : s.testBit i.val=s.testBit j.val := by
    induction p with
    | stay => rfl
    | step _ edge ih =>
      apply ih.trans
      rcases edge with e|e
      · exact eq_of_beq (List.all_eq_true.mp closed _ e)
      · exact (eq_of_beq (List.all_eq_true.mp closed _ e)).symm
  intro connected
  have eq := same (connected x y)
  change s.testBit x.val=true at hx
  change (!s.testBit y.val)=true at hy
  simp_all

private def rows := (((include_str "../k15/six-point-trap/sparse-fifteen.txt").trim.splitOn "\n").map
  fun line => ((line.splitOn " ").filter (· != "")).map String.toNat!).toArray
private def paint15 (x y : Fin 15) := Fin.ofNat' 15 (rows.findIdx (fun r => r[x.val]?==some y.val))
def sparseColoring : Coloring 15 15 where
  paint := paint15
  symm := by native_decide
  proper := by native_decide

private def at15 := [[0,1,2],[3,4,5],[6,7,9],[8,10,14],[11,12,13]]
private def at21 := [[0,2,17],[3,5,12],[1,19,20],[10,13,16],[4,6,7],[9,14,18],[8,11,15]]

def swapRecord {n} [NeZero n] (g : Coloring n n) (t : List (List Nat))
    (failed x y u v : Fin n) : Prop :=
  (∀ c,Connected (Adj (layoutEdges g t c)) ↔ c≠failed) ∧
  (∀ i j : Fin n, ∃ c,¬Connected (Adj (layoutEdges g (swapPoints i j t) c))) ∧
  (∀ c,Connected (Adj (layoutEdges g (swapPoints u v (swapPoints x y t)) c)))

private theorem record_of_tests {n} [NeZero n] (g : Coloring n n) (t : List (List Nat))
    (failed x y u v : Fin n)
    (initial : ∀ c, if c=failed then loses (layoutEdges g t c)=true else passes 0 (layoutEdges g t c)=true)
    (one : ∀ i j : Fin n, ∃ c, loses (layoutEdges g (swapPoints i j t) c)=true)
    (two : ∀ c, passes 0 (layoutEdges g (swapPoints u v (swapPoints x y t)) c)=true) :
    swapRecord g t failed x y u v := by
  refine ⟨fun c => ?_,fun i j => (one i j).imp (fun _ => lost),fun c => connected_of_passes 0 _ (two c)⟩
  by_cases eq : c=failed
  · exact iff_of_false (lost (by simpa [eq] using initial c)) (fun h => h eq)
  · exact iff_of_true (connected_of_passes 0 _ (by simpa [eq] using initial c)) eq

theorem two_swaps_K15 : swapRecord sparseColoring at15 3 0 3 0 13 :=
  record_of_tests sparseColoring at15 3 0 3 0 13 (by native_decide) (by native_decide) (by native_decide)

-- The color label is the sum of the endpoints, twice the usual round index.
theorem two_swaps_K21 : swapRecord (Periodic.roundRobin 21) at21 5 0 19 0 10 :=
  record_of_tests (Periodic.roundRobin 21) at21 5 0 19 0 10 (by native_decide) (by native_decide) (by native_decide)

#print axioms two_swaps_K15
#print axioms two_swaps_K21
end WildExact.Regroup
