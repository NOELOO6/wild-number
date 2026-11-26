import LastTwo
namespace LastTwo
set_option interpreter.prefer_native true
set_option maxHeartbeats 0
theorem row0 : audit 0 = true ∧ outsideAudit 0 = true := by native_decide
theorem row1 : audit 1 = true ∧ outsideAudit 1 = true := by native_decide
theorem row2 : audit 2 = true ∧ outsideAudit 2 = true := by native_decide
theorem row3 : audit 3 = true ∧ outsideAudit 3 = true := by native_decide
theorem row4 : audit 4 = true ∧ outsideAudit 4 = true := by native_decide
theorem row5 : audit 5 = true ∧ outsideAudit 5 = true := by native_decide
theorem row6 : audit 6 = true ∧ outsideAudit 6 = true := by native_decide
theorem transfers : cancelled = true := by native_decide
#print axioms row6
end LastTwo
