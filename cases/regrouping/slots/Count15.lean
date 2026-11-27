import QuintetCases
import SixTrap

namespace WildSlots.Quintet.K15
open WildDeletion WildExact WildCuts.OneExtra

private def colors := (List.finRange 15).map (CoreTest.colored odd)

/-- The previously checked exhaustive search is fed the ordinary edges of
this coloring. Its three counters record wins, losses and unverified cases. -/
theorem all_groupings : SixTrap.visit colors 4 32767 [] {} = ⟨125412,1275988,0⟩ := by native_decide

theorem checked_win (w : List (EdgeWalk.Edge 15)) (h : SixTrap.classify w colors = .win) :
    Works odd w.toFinset := by
  intro c x y
  exact CoreTest.to_graph _ _ _ (SixTrap.win_connected h (CoreTest.colored odd c)
    (List.mem_map.mpr ⟨c,List.mem_finRange _,rfl⟩) x y)

private theorem listed {c x y : Fin 15} (lt : x<y) (col : odd.paint x y=c) :
    (x,y)∈CoreTest.colored odd c := by
  apply List.mem_flatMap.mpr
  refine ⟨x,List.mem_finRange _,List.mem_map.mpr ⟨y,?_,rfl⟩⟩
  exact List.mem_filter.mpr ⟨List.mem_finRange _,decide_eq_true ⟨lt,col⟩⟩

theorem checked_loss (w : List (EdgeWalk.Edge 15)) (h : SixTrap.classify w colors = .loss) :
    ¬Works odd w.toFinset := by
  intro yes
  obtain ⟨m,hm,no⟩ := SixTrap.loss_disconnected h
  obtain ⟨c,_,rfl⟩ := List.mem_map.mp hm
  apply no
  intro x y
  apply (yes c x y).mapInto id
  intro a b e
  apply Walk.step (.stay _)
  rcases e with (old|old)|⟨ne,col⟩
  · exact Or.inl (List.mem_append_left _ (List.mem_toFinset.mp old))
  · exact Or.inr (List.mem_append_left _ (List.mem_toFinset.mp old))
  · rcases lt_or_gt_of_ne ne with lt|gt
    · exact Or.inl (List.mem_append_right _ (listed lt col))
    · exact Or.inr (List.mem_append_right _ (listed gt ((odd.symm _ _).trans col)))

#print axioms all_groupings
end WildSlots.Quintet.K15
