import SixTrap

namespace SecondTrap
open VertexRedraw EdgeWalk WildDeletion SixTrap
def otherRows := (numbers (include_str "two-exceptions.txt")).map List.toArray
def otherColors := otherRows.map fun m => actualEdges (fun v => Fin.ofNat' 16 m[v.val]!)
def regroupings := visit otherColors 4 32767 [] {}

theorem census : properRows otherRows=true ∧ otherRows.all (fun m => !closed 63 m)=true ∧
    (otherRows.filter (fun m => edgesInside 32831 m > 2)).length=2 ∧
    (FixedSix.starts.filter (fun blocks => blocks.all (fun t =>
      otherRows.all (fun m => !closed (t ||| 32768) m)))).length=2 ∧
    (FixedSix.triplesOn 0 15).all (fun t =>
      (otherRows.filter (closed (t ||| 32768))).length < 3)=true ∧
    (FixedSix.all.all (fun g => decide (classify (trial g) otherColors = .loss)))=true ∧
    regroupings=⟨120345,1281055,0⟩ := by native_decide
#print axioms census
end SecondTrap
