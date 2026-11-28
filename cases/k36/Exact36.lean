import ShortMoment36
import LongCuts36

namespace WildSieve.ThirtySix
open Finset WildExact EvenTriples
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
local instance (priority := 2000) exact36VertexEq {m : Nat} : DecidableEq (Fin m) :=
  (inferInstance : LinearOrder (Fin m)).toDecidableEq

/-- The short- and long-cut bounds use the same six-set label deficit.
Their sum leaves at least one partition, at every possible value of it. -/
private theorem budget (d h a b z : Nat) (labels : h+d=28560)
    (wideBound : 100*(h*8727)≤a+100*(8875*d))
    (touchBound : 7140*3104≤b+3240*d)
    (short : 12*z+5*(a*ways 8+b*ways 9)≤12*(10*h*ways 10)+(a*wideThird+b*touchThird)) :
    z+price4 d+price6+10^20≤ways 12 := by
  have first : cap24 d≤ways 8-saving false 12 8 := Nat.min_le_left _ _
  have second : cap24 d≤(6*ways 8+d*regionalCredit-1956*regionalCredit)/6 := Nat.min_le_right _ _
  have base : 1956*regionalCredit≤6*ways 8 := by decide
  have extra : 6*cap24 d+1956*regionalCredit≤6*ways 8+d*regionalCredit := by omega
  norm_num [price4,price6,pureTotal,wideThird,touchThird,regionalCredit,regionalSingle,
    regionalDouble,saving,sixWeight,sixOverlap,rootWeight,rootOverlap,ways,Nat.choose_eq_fast_choose,
    Nat.fast_choose,Nat.factorial] at short first extra ⊢
  omega

attribute [local irreducible] losses

/-- At least 10^20 partitions survive all three possible cut sizes. -/
theorem surviving_layouts_K36 (F : Factor V C) :
    10^20≤((noSix F univ) \ (losses F 4∪losses F 6)).card := by
  classical
  let B := (family F).biUnion event
  let A := noSix F univ
  have eq : B=Aᶜ := event_pattern_union F
  have deck : A.card+B.card=ways 12 := by
    rw [eq,card_compl,card_layout 12 (univ : Finset V) (by simp)]
    have cap := A.card_le_univ
    rw [card_layout 12 (univ : Finset V) (by simp)] at cap
    omega
  have price := budget (defect F) (marks F univ).card (wide F).card (touching F).card
    B.card (full_defect F).2 (wide_lower F) (touching_lower F) (short_moment F)
  have lost := (card_union_le (losses F 4) (losses F 6)).trans (Nat.add_le_add (late_four F) (late_six F))
  have split := card_sdiff_add_card_inter A (losses F 4∪losses F 6)
  have common := card_le_card (inter_subset_right : A∩(losses F 4∪losses F 6)⊆_)
  change 10^20≤(A \ (losses F 4∪losses F 6)).card
  omega

/-- Every minimum proper edge coloring of the complete graph on 36 vertices
has wild number 24. -/
theorem exact_K36 (g : Coloring 36 35) : Exact g 24 := by
  classical
  let F : Factor V C := coloringFactor g
  have count := surviving_layouts_K36 F
  obtain ⟨L,hL⟩ := card_pos.mp (Nat.lt_of_lt_of_le (by decide : 0<10^20) count)
  obtain ⟨clear,outer⟩ := mem_sdiff.mp hL
  have not4 : L∉losses F 4 := fun h => outer (mem_union_left _ h)
  have not6 : L∉losses F 6 := fun h => outer (mem_union_right _ h)
  have pass (j) (hj : j∈shortLevels∪longLevels 12) (S) (hs : S∈cuts F (Fin.last 35) 12 j) :
      L∉sealEvent S := by
    intro fail
    have lost : L∈localSeal univ S := local_seal_mem.mpr (mem_seal.mp fail)
    obtain ⟨c,hc⟩ := side_mem.mp hs
    obtain ⟨_,sz,cl⟩ := candidate_mem.mp hc
    have closed : Closed (F.f c) S := by simpa using cl
    have parity := closed_size (F.invol c) (F.moving c) closed
    have range : 0<j ∧ j≤6 := by
      rcases mem_union.mp hj with h|h
      · simp [shortLevels] at h; omega
      · obtain ⟨ra,high⟩ := mem_filter.mp h
        have := mem_range.mp ra
        omega
    by_cases small : j=2
    · exact noSix_mem.mp clear S (mark_mem.mpr ⟨subset_univ _,by omega,c,closed⟩) lost
    have hit : L∈losses F j := by
      unfold losses
      exact mem_biUnion.mpr ⟨S,hs,mem_inter.mpr ⟨clear,lost⟩⟩
    rcases (show j=4 ∨ j=6 by omega) with e|e
    · exact not4 (e ▸ hit)
    · exact not6 (e ▸ hit)
  apply exact_of_upper (pure_upper g (Fin.last 35) 12 (by decide) L pass)
  intro w le works
  have lower := even_lower (by decide : 3≤35+1) g le works
  omega

#print axioms exact_K36
end WildSieve.ThirtySix
