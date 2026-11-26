import KeepTwoScan
namespace CrossBoundary
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem retained : retain pools 0 originalBits=true := by native_decide
end CrossBoundary
