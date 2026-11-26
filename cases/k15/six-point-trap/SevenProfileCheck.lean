import SevenProfile

namespace SevenProfile
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem all_matching_profiles : allColors = true := by native_decide
theorem table_contains : ∀ i : Fin 280, (ThreeStars.sides (atLayout i)).all
    (fun s => ((table[s]?).getD 0).testBit i.val) = true := by native_decide
theorem all_geometry : ∀ i : Fin 280, ThreeStars.geometry (atLayout i) = true := by native_decide
end SevenProfile
