import SearchRedraw
namespace SearchRedraw
set_option interpreter.prefer_native true
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def batch (i : Nat) := (plans.drop (32*i)).take 32
deriving instance DecidableEq for Plan
theorem assembled : ((List.range 16).map batch).flatten = plans := by native_decide
theorem covers_all : symCover = true := by native_decide
theorem checked0 : (batch 0).all ok = true := by native_decide
theorem checked1 : (batch 1).all ok = true := by native_decide
theorem checked2 : (batch 2).all ok = true := by native_decide
theorem checked3 : (batch 3).all ok = true := by native_decide
theorem checked4 : (batch 4).all ok = true := by native_decide
theorem checked5 : (batch 5).all ok = true := by native_decide
theorem checked6 : (batch 6).all ok = true := by native_decide
theorem checked7 : (batch 7).all ok = true := by native_decide
theorem checked8 : (batch 8).all ok = true := by native_decide
theorem checked9 : (batch 9).all ok = true := by native_decide
theorem checked10 : (batch 10).all ok = true := by native_decide
theorem checked11 : (batch 11).all ok = true := by native_decide
theorem checked12 : (batch 12).all ok = true := by native_decide
theorem checked13 : (batch 13).all ok = true := by native_decide
theorem checked14 : (batch 14).all ok = true := by native_decide
theorem checked15 : (batch 15).all ok = true := by native_decide

theorem every_certificate : plans.all ok = true := by
  apply List.all_eq_true.mpr
  intro p hp
  rw [←assembled] at hp
  obtain ⟨xs,hxs,inside⟩ := List.mem_flatten.mp hp
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hxs
  have small := List.mem_range.mp hi
  have checked : (batch i).all ok = true := by
    have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first
    | exact checked0
    | exact checked1
    | exact checked2
    | exact checked3
    | exact checked4
    | exact checked5
    | exact checked6
    | exact checked7
    | exact checked8
    | exact checked9
    | exact checked10
    | exact checked11
    | exact checked12
    | exact checked13
    | exact checked14
    | exact checked15
  exact List.all_eq_true.mp checked p inside
#print axioms every_certificate
end SearchRedraw
