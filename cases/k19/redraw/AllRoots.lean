import RawMenu
namespace RawMenu
set_option interpreter.prefer_native true
set_option maxHeartbeats 0
theorem root_0 : run 0 = true := by native_decide
theorem root_1 : run 1 = true := by native_decide
theorem root_2 : run 2 = true := by native_decide
theorem root_3 : run 3 = true := by native_decide
theorem root_4 : run 4 = true := by native_decide
theorem root_5 : run 5 = true := by native_decide
theorem root_6 : run 6 = true := by native_decide
theorem root_7 : run 7 = true := by native_decide
theorem root_8 : run 8 = true := by native_decide
theorem root_9 : run 9 = true := by native_decide
theorem root_10 : run 10 = true := by native_decide
theorem root_11 : run 11 = true := by native_decide
theorem root_12 : run 12 = true := by native_decide
theorem root_13 : run 13 = true := by native_decide
theorem root_14 : run 14 = true := by native_decide
theorem root_15 : run 15 = true := by native_decide
theorem root_16 : run 16 = true := by native_decide
theorem root_17 : run 17 = true := by native_decide
theorem root_18 : run 18 = true := by native_decide
theorem all_roots : ∀ v : Fin 19, run v = true := by
  intro v
  have h : v=0 ∨ v=1 ∨ v=2 ∨ v=3 ∨ v=4 ∨ v=5 ∨ v=6 ∨ v=7 ∨ v=8 ∨ v=9 ∨ v=10 ∨ v=11 ∨ v=12 ∨ v=13 ∨ v=14 ∨ v=15 ∨ v=16 ∨ v=17 ∨ v=18 := (by decide : ∀ x : Fin 19, x=0 ∨ x=1 ∨ x=2 ∨ x=3 ∨ x=4 ∨ x=5 ∨ x=6 ∨ x=7 ∨ x=8 ∨ x=9 ∨ x=10 ∨ x=11 ∨ x=12 ∨ x=13 ∨ x=14 ∨ x=15 ∨ x=16 ∨ x=17 ∨ x=18 ) v
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact root_0
  · exact root_1
  · exact root_2
  · exact root_3
  · exact root_4
  · exact root_5
  · exact root_6
  · exact root_7
  · exact root_8
  · exact root_9
  · exact root_10
  · exact root_11
  · exact root_12
  · exact root_13
  · exact root_14
  · exact root_15
  · exact root_16
  · exact root_17
  · exact root_18
end RawMenu
