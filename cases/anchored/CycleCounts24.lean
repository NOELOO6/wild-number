import ManyFour24
import SquareVertices

namespace WildAnchor.K24
open Finset WildExact Alternating

/-- Count cycles in the graph, dividing the number of their vertices by four. -/
noncomputable def fourCount (g : Coloring 24 23) (a c : Fin 23) := (squareVertices g a c).card/4

private theorem conventions : (cycleLists 12 2 12).all (fun cs =>
    ((List.finRange 12).all (fun i => ((cyclePerm 12 cs) i).val==successor cs i.val)) &&
      decide (squareInChart (cyclePerm 12 cs)=4*cs.count 2 ∧ cs.count 2≤6))=true := by native_decide

private theorem counted (g : Coloring 24 23) (a : Fin 23) (c : {c : Fin 23 // c≠a}) :
    ∃ cs,OrderedCycles 12 2 cs ∧ (∃ w,AlternatingChart g a c.val (cyclePerm 12 cs) w) ∧
      fourCount g a c=cs.count 2 ∧ cs.count 2≤6 := by
  have convention := List.all_eq_true.mpr (fun cs hcs =>
    (Bool.and_eq_true_iff.mp (List.all_eq_true.mp conventions cs hcs)).1)
  obtain ⟨cs,ord,w,chart⟩ := charts_of_periods g a c.val (m:=12) (by decide) 2
    (by decide) (min_two g a c.val c.property) convention
  have h := of_decide_eq_true (Bool.and_eq_true_iff.mp
    (List.all_eq_true.mp conventions cs (cycle_member (by decide) ord))).2
  refine ⟨cs,ord,⟨w,chart⟩,?_,h.2⟩
  rw [fourCount,square_in_chart g a c.val _ w chart,h.1]
  omega

/-- An anchor with at most two or at least 105 alternating four-cycles
in total certifies the conjectured wild number. -/
theorem exact_of_four_count (g : Coloring 24 23) (a : Fin 23)
    (h : (∑ c : {c : Fin 23 // c≠a},fourCount g a c)≤2 ∨
      105≤(∑ c : {c : Fin 23 // c≠a},fourCount g a c)) : Exact g 16 := by
  classical
  choose cs ord charts number cap using counted g a
  simp only [number] at h
  rcases h with few|many
  · obtain ⟨d,hd⟩ : ∃ d : Fin 23,d≠a := by
      by_cases e : a=0
      · exact ⟨1,e ▸ (by decide)⟩
      · exact ⟨0,Ne.symm e⟩
    obtain ⟨e,frame⟩ := frame_of_charts g a _ ⟨d,hd⟩ charts
    exact exact g a e cs ord frame few
  · apply FourCycles.exact g a cs ord charts
    have together : (∑ c,(6-(cs c).count 2+(cs c).count 2))=∑ _c : {c : Fin 23 // c≠a},6 :=
      sum_congr rfl (fun c _ => Nat.sub_add_cancel (cap c))
    have size : Fintype.card {c : Fin 23 // c≠a}=22 := by simp
    rw [sum_add_distrib] at together
    simp only [sum_const,card_univ,size,nsmul_eq_mul] at together
    omega

#print axioms exact_of_four_count
end WildAnchor.K24
