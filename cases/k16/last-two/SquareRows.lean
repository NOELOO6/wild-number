import SquarePair
namespace SquarePair
set_option interpreter.prefer_native true
set_option maxHeartbeats 0
theorem covered : allOrbits = true := by native_decide
theorem segment0 : batch 0 12 = true := by native_decide
theorem segment12 : batch 12 24 = true := by native_decide
theorem segment24 : batch 24 36 = true := by native_decide
theorem segment36 : batch 36 48 = true := by native_decide
theorem segment48 : batch 48 60 = true := by native_decide
theorem segment60 : batch 60 72 = true := by native_decide
theorem segment72 : batch 72 84 = true := by native_decide
theorem segment84 : batch 84 96 = true := by native_decide
theorem segment96 : batch 96 108 = true := by native_decide
theorem segment108 : batch 108 120 = true := by native_decide
theorem segment120 : batch 120 132 = true := by native_decide
theorem segment132 : batch 132 144 = true := by native_decide
theorem segment144 : batch 144 156 = true := by native_decide
theorem segment156 : batch 156 168 = true := by native_decide
theorem segment168 : batch 168 169 = true := by native_decide
#print axioms covered
#print axioms segment168
end SquarePair
