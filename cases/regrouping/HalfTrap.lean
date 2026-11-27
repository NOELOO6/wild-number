import SwapExamples

namespace WildExact.Regroup.HalfTrap
open WildDeletion EdgeWalk

def initial := [[0,2,3],[1,4,5],[6,7,9],[8,10,12],[11,13,14]]
def merged := [[0,2,3],[1,4,5],[6,7,8,9,10,11,12,13,14]]
def repaired := [[0,2,3],[11,13,14],[1,4,7],[5,6,9],[8,10,12]]

private theorem initialCheck : ∀ c : Fin 15,
    if c=10 then loses (layoutEdges sparseColoring initial c)=true
    else passes 0 (layoutEdges sparseColoring initial c)=true := by native_decide

theorem initial_colors (c : Fin 15) :
    Connected (Adj (layoutEdges sparseColoring initial c)) ↔ c≠10 := by
  by_cases eq : c=10
  · exact iff_of_false (lost (by simpa [eq] using initialCheck c)) (fun h => h eq)
  · exact iff_of_true (connected_of_passes 0 _ (by simpa [eq] using initialCheck c)) eq

private theorem mergeCheck : ∀ c : Fin 15, passes 0 (layoutEdges sparseColoring merged c)=true := by native_decide
private theorem repairCheck : ∀ c : Fin 15, passes 0 (layoutEdges sparseColoring repaired c)=true := by native_decide

theorem merged_colors (c : Fin 15) : Connected (Adj (layoutEdges sparseColoring merged c)) :=
  connected_of_passes 0 _ (mergeCheck c)

theorem repaired_colors (c : Fin 15) : Connected (Adj (layoutEdges sparseColoring repaired c)) :=
  connected_of_passes 0 _ (repairCheck c)

/-- The temporary root 15 is joined to 3, the vertex missing color 10. -/
def augmentedEdges : List (Edge 16) :=
  (15,3) :: (layoutEdges sparseColoring initial 10).map (fun e => (e.1.castSucc,e.2.castSucc))

theorem missing_ten : ∀ x : Fin 15,x≠3 → sparseColoring.paint 3 x≠10 := by native_decide

def blockIndex (v : Fin 16) : Fin 6 :=
  if v=15 then 0 else if v=0 ∨ v=2 ∨ v=3 then 1
  else if v=1 ∨ v=4 ∨ v=5 then 2 else if v=6 ∨ v=7 ∨ v=9 then 3
  else if v=8 ∨ v=10 ∨ v=12 then 4 else 5

def piece (g : Fin 6) := g=2 || g=5

private theorem componentChecks :
    (∀ e∈augmentedEdges,piece (blockIndex e.1)=piece (blockIndex e.2)) ∧
    ∀ p q : Fin 16,piece (blockIndex p)=piece (blockIndex q) →
      (run augmentedEdges 16 (2^p.val)).testBit q.val=true := by native_decide

theorem original_pieces (p q : Fin 16) :
    Walk (Adj augmentedEdges) p q ↔ piece (blockIndex p)=piece (blockIndex q) := by
  constructor
  · intro walk
    induction walk with
    | stay => rfl
    | step _ e ih =>
      apply ih.trans
      rcases e with h|h
      · exact componentChecks.1 _ h
      · exact (componentChecks.1 _ h).symm
  · intro eq
    exact walk_of_seen p q augmentedEdges (componentChecks.2 p q eq)

/-- The selected groups 3, 4 and 5 take exactly half of each original
component of the failed color. Every other color has one component. -/
theorem balanced_selection (b : Bool) :
    2*((Finset.univ : Finset (Fin 6)).filter (fun g => piece g=b ∧ 3≤g.val)).card =
      ((Finset.univ : Finset (Fin 6)).filter (fun g => piece g=b)).card := by
  cases b <;> decide

/-- Keep the first two triples. The third cell consists of 11 and its two
new partners. The fourth cell contains all six remaining vertices. -/
def cell (x y v : Fin 15) : Fin 4 :=
  if v=0 ∨ v=2 ∨ v=3 then 0
  else if v=1 ∨ v=4 ∨ v=5 then 1
  else if v=11 ∨ v=x ∨ v=y then 2 else 3

private def side (m : Fin 4) (i : Fin 4) : Bool :=
  i=2 || (i=0 && m.val.testBit 0) || (i=1 && m.val.testBit 1)

private theorem witnesses : ∀ x y : Fin 15, 6≤x.val → 6≤y.val → x≠11 → y≠11 → x≠y →
    ∃ c : Fin 15, ∃ m : Fin 4,
      (∃ p q : Fin 15, side m (cell x y p) ≠ side m (cell x y q)) ∧
      ∀ p q : Fin 15, p≠q → sparseColoring.paint p q=c →
        side m (cell x y p)=side m (cell x y q) := by native_decide

/-- Every repartition of the nine into three triples fails. The result even
allows arbitrary wild edges among the six vertices outside the triple of 11. -/
theorem anchored_redraw_fails (x y : Fin 15) (hx : 6≤x.val) (hy : 6≤y.val)
    (px : x≠11) (py : y≠11) (xy : x≠y) :
    ∃ c : Fin 15, ∀ w : Lines 15,
      (∀ e∈w,cell x y e.1=cell x y e.2) → ¬Connected (Joined sparseColoring w c) := by
  obtain ⟨c,m,⟨p,q,different⟩,closed⟩ := witnesses x y hx hy px py xy
  refine ⟨c,fun w grouped connected => different ?_⟩
  have same {a b} (h : Walk (Joined sparseColoring w c) a b) :
      side m (cell x y a)=side m (cell x y b) := by
    induction h with
    | stay => rfl
    | step _ e ih =>
      apply ih.trans
      rcases e with (h|h)|⟨ne,col⟩
      · exact congrArg (side m) (grouped _ h)
      · exact (congrArg (side m) (grouped _ h)).symm
      · exact closed _ _ ne col
  exact same (connected p q)

#print axioms anchored_redraw_fails
end WildExact.Regroup.HalfTrap
