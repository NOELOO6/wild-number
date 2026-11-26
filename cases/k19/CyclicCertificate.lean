import Rotations
namespace K19Rotation
open EdgeWalk WildDeletion
set_option interpreter.prefer_native true
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem counts : starters.length = 25905 ∧ layouts.length = 43 := by native_decide
theorem all_proper : starters.all properColoring = true := by native_decide
theorem all_listed : rows.map Prod.fst = starters := by native_decide
theorem checked : rows.all rowOK = true := by native_decide

theorem thirteen_for_every_starter (s : Edges) (h : Starter points.tail [] s) (hn : s.length = 9) :
    ∃ w : Edges, w.length = 13 ∧ ∀ c : V, Connected (Adj (w ++ shifted s c)) := by
  have hs : s ∈ starters := exhaustive h 9 (by omega)
  rw [← all_listed] at hs
  obtain ⟨⟨m,i⟩,hi,eq⟩ := List.mem_map.mp hs
  change m = s at eq
  subst m
  obtain ⟨len, pass⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp checked (s,i) hi)
  refine ⟨_, beq_iff_eq.mp len, fun c => connected_of_passes 0 _ ?_⟩
  exact List.all_eq_true.mp pass c (by revert c; decide)
def roundRobin : Edges := [(1,18),(2,17),(3,16),(4,15),(5,14),(6,13),(7,12),(8,11),(9,10)]
theorem example_paths : (layouts[6]!).length = 13 ∧ ∀ c : V,
    Connected (Adj (layouts[6]! ++ shifted roundRobin c)) := by
  have h : works roundRobin layouts[6]! = true := by native_decide
  obtain ⟨len,ok⟩ := Bool.and_eq_true_iff.mp h
  exact ⟨beq_iff_eq.mp len, fun c => connected_of_passes 0 _ (List.all_eq_true.mp ok c (by revert c; decide))⟩
#print axioms thirteen_for_every_starter
end K19Rotation
