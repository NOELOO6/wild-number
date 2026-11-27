import NineBounds

namespace WildExact.K13
open WildExact
theorem found {a b c : Nat} (h : Nine.hit a b c=true) : grouping a b c ∈ layouts := by
  have ha : a<b ∧ b<c ∧ c<84 := by
    simp only [Nine.hit,Bool.and_eq_true,decide_eq_true_eq] at h
    exact ⟨h.1.1.1,h.1.1.2,h.1.2⟩
  exact List.mem_flatMap.mpr ⟨a,List.mem_range.mpr (by omega),List.mem_flatMap.mpr
    ⟨b,List.mem_range.mpr (by omega),List.mem_map.mpr ⟨c,List.mem_filter.mpr ⟨List.mem_range.mpr ha.2.2,h⟩,rfl⟩⟩⟩

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem build_upper (g : Coloring 13 13) (capsChecked : fastCheck=true) (pathsChecked : pathCheck=true)
    (nine : ∀ b : Nine.Family, Nine.Caps b → ¬ Nine.Hits b) : Upper g 9 := by
  obtain ⟨h,ok,back⟩ := Four.normalize_four g
  apply back
  obtain ⟨rs,hr⟩ := choose_rows (augment (by decide) h)
  have caps := caps_of_graph h ok rs hr capsChecked
  have survivor := nine (badFamily rs) caps
  unfold Nine.Hits at survivor
  push_neg at survivor
  obtain ⟨a,b,c,hit,one,two,three⟩ := survivor
  let w := grouping a b c
  have legal : ∀ x∈layouts, x.lines.length≤9 ∧ ∀ e∈x.lines,e.1<e.2 := by native_decide
  have mem : w∈layouts := found hit
  apply from_rows (by decide) h rs (fun j => (hr j).2) 0 w.lines 9 (legal _ mem).1 (legal _ mem).2
  intro j
  have clear (i : Nat) (no : badFamily rs i≠true) : (blocked (rs j)).contains i=false := by
    cases eq : (blocked (rs j)).contains i
    · rfl
    · exact False.elim (no (List.any_eq_true.mpr ⟨j,List.mem_finRange _,eq⟩))
  have noRep := no_pair_of_weight h ok rs hr j
  have all := List.all_eq_true.mp pathsChecked _ (hr j).1
  simp only [noRep,Bool.false_or,Id.run] at all
  have pass := List.all_eq_true.mp all w mem
  simpa only [w,grouping,clear a one,clear b two,clear c three,Bool.false_or,passesRow] using pass

end WildExact.K13
