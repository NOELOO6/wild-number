import ExteriorRows
namespace ExteriorRows
open VertexRedraw ThreeStars EdgeWalk WildDeletion
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem every_row : allRows = true := by native_decide
theorem sideTable : ∀ j i, (sides (layout j i)).all
    (fun s => (bySide[s]?.getD 0).testBit (index j i))=true := by native_decide
theorem shapes : ∀ j i, geometry (layout j i) = true ∧
    (layout j i).groups ∈ FixedSix.all ∧ (wild (layout j i)).length=10 ∧
    (wild (layout j i)).Nodup := by native_decide
theorem options_table : ∀ c : C, opts[c.val]!.toList=BoundaryOptions.possible lock c := by native_decide
end ExteriorRows
