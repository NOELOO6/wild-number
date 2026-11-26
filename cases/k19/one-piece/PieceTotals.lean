import PartitionCounts
namespace WildPieces
open Finset
set_option maxRecDepth 50000
set_option maxHeartbeats 0

theorem two_cells : total 2 = 13218228559872000 := by native_decide
theorem three_cells : total 3 = 468787544064000 := by native_decide
theorem four_cells : total 4 = 5643509760000 := by native_decide

end WildPieces
