import SevenBalance
namespace SevenProfile
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem all_totals : visit accounting 16 VertexRedraw.points [] = true := by native_decide
end SevenProfile
