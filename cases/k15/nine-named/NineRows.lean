import NineNamed
namespace NineNamed
set_option interpreter.prefer_native true
set_option maxHeartbeats 0
theorem no_net_transfer : cancelled = true := by native_decide
theorem row0 : check 0 = true := by native_decide
theorem row1 : check 1 = true := by native_decide
theorem row2 : check 2 = true := by native_decide
theorem row3 : check 3 = true := by native_decide
theorem row4 : check 4 = true := by native_decide
theorem row5 : check 5 = true := by native_decide
theorem row6 : check 6 = true := by native_decide
theorem row7 : check 7 = true := by native_decide
theorem row8 : check 8 = true := by native_decide
theorem row9 : check 9 = true := by native_decide
theorem row10 : check 10 = true := by native_decide
#print axioms row10
end NineNamed
