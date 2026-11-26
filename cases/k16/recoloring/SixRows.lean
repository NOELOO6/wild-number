import Recolor
namespace SixColors
set_option interpreter.prefer_native true
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def batch0 := (plans.drop 0).take 89
theorem batch0_works : batch0.all rowOK = true := by native_decide
def batch1 := (plans.drop 89).take 89
theorem batch1_works : batch1.all rowOK = true := by native_decide
def batch2 := (plans.drop 178).take 89
theorem batch2_works : batch2.all rowOK = true := by native_decide
def batch3 := (plans.drop 267).take 89
theorem batch3_works : batch3.all rowOK = true := by native_decide
def batch4 := (plans.drop 356).take 89
theorem batch4_works : batch4.all rowOK = true := by native_decide
def batch5 := (plans.drop 445).take 89
theorem batch5_works : batch5.all rowOK = true := by native_decide
def batch6 := (plans.drop 534).take 89
theorem batch6_works : batch6.all rowOK = true := by native_decide
def batch7 := (plans.drop 623).take 89
theorem batch7_works : batch7.all rowOK = true := by native_decide
def batches := [batch0, batch1, batch2, batch3, batch4, batch5, batch6, batch7]
theorem cover_rows : batches.flatten.map (fun p => (p.root,p.mask,p.pivot,p.ids)) =
    plans.map (fun p => (p.root,p.mask,p.pivot,p.ids)) := by native_decide
theorem all_rows : plans.all rowOK = true := by
  apply List.all_eq_true.mpr
  intro p hp
  have h := List.mem_map_of_mem (f := fun p : Plan => (p.root,p.mask,p.pivot,p.ids)) hp
  rw [← cover_rows] at h
  obtain ⟨q,hq,eq⟩ := List.mem_map.mp h
  have same : q = p := by cases p; cases q; simp_all
  subst q
  obtain ⟨bs,hbs,hm⟩ := List.mem_flatten.mp hq
  have ok : ∀ s ∈ batches, s.all rowOK = true := by
    intro s hs
    simp only [batches,List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact batch0_works
    · exact batch1_works
    · exact batch2_works
    · exact batch3_works
    · exact batch4_works
    · exact batch5_works
    · exact batch6_works
    · exact batch7_works
  exact List.all_eq_true.mp (ok bs hbs) p hm
end SixColors
