import Prescribed
namespace Prescribed
set_option interpreter.prefer_native true
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem rooted_0 : checkRow true 0 = true := by native_decide
theorem rooted_1 : checkRow true 1 = true := by native_decide
theorem rooted_2 : checkRow true 2 = true := by native_decide
theorem rooted_3 : checkRow true 3 = true := by native_decide
theorem rooted_4 : checkRow true 4 = true := by native_decide
theorem rooted_5 : checkRow true 5 = true := by native_decide
theorem rooted_6 : checkRow true 6 = true := by native_decide
theorem rooted_7 : checkRow true 7 = true := by native_decide
theorem rooted_8 : checkRow true 8 = true := by native_decide
theorem rooted_9 : checkRow true 9 = true := by native_decide
theorem rooted_10 : checkRow true 10 = true := by native_decide
theorem free_0 : checkRow false 0 = true := by native_decide
theorem free_1 : checkRow false 1 = true := by native_decide
theorem free_2 : checkRow false 2 = true := by native_decide
theorem free_3 : checkRow false 3 = true := by native_decide
theorem free_4 : checkRow false 4 = true := by native_decide
theorem free_5 : checkRow false 5 = true := by native_decide
theorem free_6 : checkRow false 6 = true := by native_decide
end Prescribed
