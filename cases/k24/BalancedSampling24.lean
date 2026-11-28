import GraphRegions24
import CutPrices24
import RegionLayouts
import LongCredit

namespace WildSieve.TwentyFour
open Finset EvenTriples WildExact
set_option maxRecDepth 8000
set_option maxHeartbeats 1000000
local instance (priority := 2000) balancedEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq
abbrev Deck := Layout (univ : Finset V)

noncomputable abbrev anchors (F : Factor V C) (c : C) := candidates F c ∅ univ 12

theorem anchor_card (F : Factor V C) (c : C) : (anchors F c).card=924 := by
  rw [anchors,show 12=2*6 by decide,candidate_pairs,SixCounts.full_pairs]
  decide

theorem side_card (L : Finset V) (sz : L.card=12) :
    (localSeal univ L).card=ways 4*ways 4 := by
  rw [local_seal_ways _ _ (subset_univ _),card_univ,Fintype.card_fin,sz]
  rfl

noncomputable def survivingSide (F : Factor V C) (L : Finset V) := noSix F univ∩localSeal univ L

/-- A surviving balanced failure is counted with the side avoiding a fixed point. -/
noncomputable def lateBad (F : Factor V C) :=
  (cuts F (Fin.last 23) 8 4).biUnion (survivingSide F)

private theorem both_sides (F : Factor V C) {c : C} {D : Deck} {L : Finset V}
    (anchor : L∈anchors F c) (hit : D∈survivingSide F L) :
    Lᶜ∈anchors F c ∧ D∈survivingSide F Lᶜ := by
  obtain ⟨_,sz,cl⟩ := candidate_mem.mp anchor
  simp only [empty_union] at cl
  have outside : Closed (F.f c) Lᶜ := fun v hv => mem_compl.mpr fun h =>
    mem_compl.mp hv (F.invol c v ▸ cl _ h)
  refine ⟨candidate_mem.mpr ⟨subset_univ _,by rw [card_compl,Fintype.card_fin,sz],
    by simpa only [empty_union] using outside⟩,mem_inter.mpr ⟨(mem_inter.mp hit).1,?_⟩⟩
  have whole := (seal_whole (subset_univ L) D).mp (mem_inter.mp hit).2
  exact (seal_whole (subset_univ Lᶜ) D).mpr (fun b hb v vb vs x xb =>
    mem_compl.mpr (fun xs => mem_compl.mp vs (whole b hb x xb xs vb)))

attribute [local irreducible] noSix localSeal candidates

/-- Every balanced failure surviving the six-point test has two distinct oriented witnesses. -/
theorem double_sample (F : Factor V C) :
    2*(lateBad F).card ≤ ∑ c,∑ L∈anchors F c,(survivingSide F L).card := by
  classical
  let count (D : Deck) (c : C) := ((anchors F c).filter (fun L => D∈survivingSide F L)).card
  have per (D : Deck) (hit : D∈lateBad F) : 2≤∑ c,count D c := by
    obtain ⟨L,cut,side⟩ := mem_biUnion.mp hit
    obtain ⟨c,hc⟩ := side_mem.mp cut
    obtain ⟨_,sz,cl⟩ := candidate_mem.mp hc
    have ha : L∈anchors F c := candidate_mem.mpr ⟨subset_univ _,sz,cl⟩
    obtain ⟨other,also⟩ := both_sides F ha side
    have different : L≠Lᶜ := by
      intro eq
      have h : (0 : V)∈L ↔ (0 : V)∈Lᶜ := by conv_lhs => rw [eq]
      simp only [mem_compl] at h
      tauto
    have inc : ({L,Lᶜ} : Finset (Finset V)) ⊆ (anchors F c).filter (fun S => D∈survivingSide F S) := by
      simpa only [insert_subset_iff,singleton_subset_iff,mem_filter] using And.intro ⟨ha,side⟩ ⟨other,also⟩
    exact (show 2≤count D c by simpa [count,different] using card_le_card inc).trans
      (single_le_sum (f:=count D) (fun _ _ => Nat.zero_le _) (mem_univ c))
  have a := sum_le_sum per
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id] at a
  rw [Nat.mul_comm] at a
  apply a.trans
  calc
    _ ≤ ∑ D : Deck,∑ c,count D c := sum_le_sum_of_subset (subset_univ _)
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro c _
      simp only [count,card_eq_sum_ones,sum_filter]
      rw [sum_comm]
      apply sum_congr rfl
      intro L _
      simp

/-- The graph reduction from a surviving layout to sixteen wild edges. -/
theorem exact_of_survivor (g : Coloring 24 23) (D : Deck)
    (short : D∈noSix (coloringFactor g) univ) (long : D∉lateBad (coloringFactor g)) : Exact g 16 := by
  classical
  let F : Factor V C := coloringFactor g
  have pass (j) (hj : j∈shortLevels∪longLevels 8) (S) (hs : S∈cuts F (Fin.last 23) 8 j) :
      D∉sealEvent S := by
    intro fail
    have lost : D∈localSeal univ S := local_seal_mem.mpr (mem_seal.mp fail)
    obtain ⟨c,hc⟩ := side_mem.mp hs
    obtain ⟨_,sz,cl⟩ := candidate_mem.mp hc
    have closed : Closed (F.f c) S := by simpa using cl
    have parity := closed_size (F.invol c) (F.moving c) closed
    have range : 0<j ∧ j≤4 := by
      rcases mem_union.mp hj with h|h
      · simp [shortLevels] at h; omega
      · obtain ⟨ra,high⟩ := mem_filter.mp h
        have := mem_range.mp ra
        omega
    rcases (show j=2 ∨ j=4 by omega) with rfl|rfl
    · exact noSix_mem.mp short _ (mark_mem.mpr ⟨subset_univ _,sz,c,closed⟩) lost
    · exact long (mem_biUnion.mpr ⟨S,hs,mem_inter.mpr ⟨short,lost⟩⟩)
  exact exact_of_upper (pure_upper g (Fin.last 23) 8 (by decide) D pass) (fun w hw wins => by
    have low := even_lower (by decide : 3≤23+1) g hw wins
    omega)

#print axioms double_sample
#print axioms exact_of_survivor
end WildSieve.TwentyFour
