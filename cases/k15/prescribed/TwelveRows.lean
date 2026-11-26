import Twelve
namespace WildTwelve
set_option maxHeartbeats 0
set_option interpreter.prefer_native true
theorem row_0 : check 0 = true := by native_decide
theorem row_1 : check 1 = true := by native_decide
theorem row_2 : check 2 = true := by native_decide
theorem row_3 : check 3 = true := by native_decide
theorem row_4 : check 4 = true := by native_decide
theorem row_5 : check 5 = true := by native_decide
theorem row_6 : check 6 = true := by native_decide
theorem row_7 : check 7 = true := by native_decide
theorem row_8 : check 8 = true := by native_decide
theorem row_9 : check 9 = true := by native_decide
theorem row_10 : check 10 = true := by native_decide
theorem transfers_cancel : transfersOK = true := by native_decide
#print axioms row_10
end WildTwelve
