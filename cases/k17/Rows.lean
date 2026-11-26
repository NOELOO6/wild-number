import ThirdColors

namespace K17
set_option interpreter.prefer_native true
set_option maxRecDepth 200000
set_option maxHeartbeats 0

private theorem row00 : checkCase 0 = true := by native_decide
private theorem row01 : checkCase 1 = true := by native_decide
private theorem row02 : checkCase 2 = true := by native_decide
private theorem row03 : checkCase 3 = true := by native_decide
private theorem row04 : checkCase 4 = true := by native_decide
private theorem row05 : checkCase 5 = true := by native_decide
private theorem row06 : checkCase 6 = true := by native_decide
private theorem row07 : checkCase 7 = true := by native_decide
private theorem row08 : checkCase 8 = true := by native_decide
private theorem row09 : checkCase 9 = true := by native_decide
private theorem row10 : checkCase 10 = true := by native_decide
private theorem row11 : checkCase 11 = true := by native_decide
private theorem row12 : checkCase 12 = true := by native_decide
private theorem row13 : checkCase 13 = true := by native_decide
private theorem row14 : checkCase 14 = true := by native_decide

theorem all_pair_types (i : Fin 15) : checkCase i.val = true := by
  have hi := i.isLt
  have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9 ∨ i.val = 10 ∨ i.val = 11 ∨ i.val = 12 ∨ i.val = 13 ∨ i.val = 14 := by omega
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h]
  · exact row00
  · exact row01
  · exact row02
  · exact row03
  · exact row04
  · exact row05
  · exact row06
  · exact row07
  · exact row08
  · exact row09
  · exact row10
  · exact row11
  · exact row12
  · exact row13
  · exact row14

#print axioms all_pair_types
end K17
