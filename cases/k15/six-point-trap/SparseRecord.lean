import SixTrap
namespace SparseRecord
open VertexRedraw EdgeWalk WildDeletion

def rows := (numbers (include_str "sparse-sixteen.txt")).map List.toArray
def ordinary := rows.map fun m => actualEdges (fun v => Fin.ofNat' 16 m[v.val]!)
def verdict (g : List Nat) := SixTrap.classify (trial g) ordinary
def counts := FixedSix.starts.map fun a =>
  (FixedSix.endings.filter (fun b => verdict (a++b) == .win)).length

theorem record : properRows rows = true ∧
    rows.all (fun m => SixTrap.edgesInside FixedSix.seven m ≤ 2) = true ∧
    (FixedSix.all.filter (fun g => verdict g == .win)).length = 16 ∧
    (FixedSix.all.filter (fun g => verdict g == .loss)).length = 2784 ∧
    counts.mergeSort = [0,0,0,0,0,0,0,4,4,8] := by native_decide

theorem paths {g : List Nat} (h : verdict g = .win) :
    ∀ m ∈ ordinary, Connected (Adj (trial g ++ m)) := SixTrap.win_connected h
theorem cut {g : List Nat} (h : verdict g = .loss) :
    ∃ m ∈ ordinary, ¬ Connected (Adj (trial g ++ m)) := SixTrap.loss_disconnected h
#print axioms record
end SparseRecord
