import RedrawModel
namespace RedrawModel
open VertexRedraw EdgeWalk WildDeletion
set_option maxRecDepth 200000
set_option maxHeartbeats 0
theorem checked : formula.length=123493 ∧ tags.size=formula.length ∧ census=true := by native_decide
theorem lookups : (∀ c x y, em c x y = eMask c x y) ∧
    (List.range groups.size).all (fun i => colors.all (fun c =>
      wm i c == wMask c groups[i]!)) = true := by native_decide
theorem groups_valid : groups.toList.all (fun g => FixedSix.all.contains g &&
    decide ((trial g).length=10 ∧ (trial g).Nodup)) = true := by native_decide
theorem rows_full : colors.all (fun c => (opts c).all (fun m => points.all
    (fun x => points.any (fun y => hasEdge m x y)))) = true := by native_decide
end RedrawModel
