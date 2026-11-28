import NoFour30
import MatchingCycles
import Anchor24

namespace WildAnchor
open WildExact Alternating

private theorem convention (m : Nat) (hm : m=12 ∨ m=15) :
    (cycleLists m 3 m).all (fun cs => (List.finRange m).all fun i =>
      ((cyclePerm m cs) i).val==successor cs i.val)=true := by
  rcases hm with rfl|rfl <;> native_decide

/-- A condition on the original edge coloring alone. An anchor avoiding
alternating four-cycles supplies its own sorted cycle coordinates. -/
theorem K30.exact_of_no_four_cycle (g : Coloring 30 29) (a : Fin 29)
    (none : ∀ c,c≠a → NoFourCycle g a c) : Exact g 20 := by
  have all (c : {c : Fin 29 // c≠a}) := charts_of_periods g a c.val (m:=15) (by decide) 3
    (by decide) (min_three g a c.val c.property (none _ c.property)) (convention _ (Or.inr rfl))
  choose cs ord w chart using all
  exact K30.exact_no_four g a cs ord (fun c => ⟨w c,chart c⟩)

/-- The coordinate-free no-four-cycle case at K24. -/
theorem K24.exact_of_no_four_cycle (g : Coloring 24 23) (a : Fin 23)
    (none : ∀ c,c≠a → NoFourCycle g a c) : Exact g 16 := by
  have all (c : {c : Fin 23 // c≠a}) := charts_of_periods g a c.val (m:=12) (by decide) 3
    (by decide) (min_three g a c.val c.property (none _ c.property)) (convention _ (Or.inl rfl))
  choose cs ord w chart using all
  have ex : ∃ c : Fin 23,c≠a := by
    by_cases h : a=0
    · exact ⟨1,h ▸ (by decide)⟩
    · exact ⟨0,Ne.symm h⟩
  obtain ⟨c,hc⟩ := ex
  obtain ⟨e,frame⟩ := frame_of_charts g a _ ⟨c,hc⟩ (fun c => ⟨w c,chart c⟩)
  apply K24.exact g a e cs (fun d => ⟨(ord d).1,fun l hl => le_trans (by decide : 2≤3) ((ord d).2.1 l hl),(ord d).2.2⟩) frame
  have no (d) : 2∉cs d := fun h => (by decide : ¬3≤2) ((ord d).2.1 2 h)
  simp [List.count_eq_zero_of_not_mem,no]

#print axioms K30.exact_of_no_four_cycle
#print axioms K24.exact_of_no_four_cycle
end WildAnchor
