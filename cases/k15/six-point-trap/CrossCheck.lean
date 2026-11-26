import CrossBoundary
namespace CrossBoundary
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem census : SixBoundary.scan pools 0 SixBoundary.initial = ⟨854689,0⟩ := by native_decide
end CrossBoundary
