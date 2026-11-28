import LayoutMoments30
import Budget30

namespace WildSieve.Thirty.Graph
open Finset WildExact EvenTriples
local instance (priority := 2000) budgetEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq
set_option maxHeartbeats 1000000
set_option maxRecDepth 12000

/-- All six-point cuts together, with a saving for every surplus closing label. -/
theorem short_affine (F : Factor V C) :
    3*(shortBad F).card+115956463392000*defect F≤2723081975597984000 := by
  have short := short_count F
  have wideBound := wide_lower F
  have touchBound := touching_lower F
  have labels := (full_defect F).2
  change (marks F univ).card+defect F=13195 at labels
  norm_num [ways,Nat.choose_eq_fast_choose,Nat.fast_choose,Nat.factorial] at short
  omega

/-- After removing six-point cuts, only a closed union of four triples can remain. -/
noncomputable def lateBad (F : Factor V C) :=
  (cuts F (Fin.last 29) 10 4).biUnion (fun S => noSix F univ∩localSeal univ S)

theorem shortBad_eq (F : Factor V C) : shortBad F=(noSix F univ)ᶜ := by
  unfold shortBad
  exact @SixCounts.event_pattern_union 30 29 F

attribute [local irreducible] shortBad lateBad noSix

theorem exact_of_survivor (g : Coloring 30 29) (D : Deck)
    (short : D∉shortBad (coloringFactor g)) (long : D∉lateBad (coloringFactor g)) : Exact g 20 := by
  classical
  let F : Factor V C := coloringFactor g
  have small : D∈noSix F univ := by
    change D∉shortBad F at short
    rw [shortBad_eq,mem_compl] at short
    exact not_not.mp short
  have pass (j) (hj : j∈shortLevels∪longLevels 10) (S) (hs : S∈cuts F (Fin.last 29) 10 j) :
      D∉sealEvent S := by
    intro fail
    have lost : D∈localSeal univ S := local_seal_mem.mpr (mem_seal.mp fail)
    obtain ⟨c,hc⟩ := side_mem.mp hs
    obtain ⟨_,sz,cl⟩ := candidate_mem.mp hc
    have closed : Closed (F.f c) S := by simpa using cl
    have parity := closed_size (F.invol c) (F.moving c) closed
    have range : 0<j ∧ j≤5 := by
      rcases mem_union.mp hj with h|h
      · simp [shortLevels] at h; omega
      · obtain ⟨ra,high⟩ := mem_filter.mp h
        have := mem_range.mp ra
        omega
    rcases (show j=2 ∨ j=4 by omega) with rfl|rfl
    · exact noSix_mem.mp small _ (mark_mem.mpr ⟨subset_univ _,sz,c,closed⟩) lost
    · apply long
      unfold lateBad
      exact mem_biUnion.mpr ⟨S,hs,mem_inter.mpr ⟨small,lost⟩⟩
  exact exact_of_upper (pure_upper g (Fin.last 29) 10 (by decide) D pass) (fun w hw wins => by
    have low := even_lower (by decide : 3≤29+1) g hw wins
    omega)

theorem survivors (F : Factor V C) :
    ((shortBad F∪lateBad F)ᶜ).card+(shortBad F).card+(lateBad F).card=ways 10 := by
  classical
  have apart : Disjoint (shortBad F) (lateBad F) := by
    apply disjoint_left.mpr
    intro D h bad
    unfold lateBad at bad
    obtain ⟨S,_,inside⟩ := mem_biUnion.mp bad
    have together := (mem_inter.mp inside).1
    rw [shortBad_eq,mem_compl] at h
    exact h together
  have pos := card_le_univ (shortBad F∪lateBad F)
  rw [card_compl,card_layout 10 (univ : Finset V) (by decide),card_union_of_disjoint apart]
  rw [card_layout 10 (univ : Finset V) (by decide),card_union_of_disjoint apart] at pos
  omega

private theorem of_positive (g : Coloring 30 29)
    (win : 0<((shortBad (coloringFactor g)∪lateBad (coloringFactor g))ᶜ).card) : Exact g 20 := by
  obtain ⟨D,hd⟩ := card_pos.mp win
  have avoid := mem_compl.mp hd
  exact exact_of_survivor g D (fun h => avoid (mem_union_left _ h)) (fun h => avoid (mem_union_right _ h))

/-- A checked unrestricted graph implication. Its hypothesis is the bound on
surviving twelve-point cuts from the long-cut sampling argument. -/
theorem winning_count_of_long (F : Factor V C)
    (long : ((lateBad F).card : ℚ)/(ways 10 : ℚ)≤longMass*(longPrice+(defect F : ℚ)/18000)) :
    2211739995828567 ≤ ((shortBad F∪lateBad F)ᶜ).card := by
  have a := short_affine F
  have s : 3*((shortBad F).card : ℚ)+115956463392000*(defect F : ℚ)≤2723081975597984000 := by exact_mod_cast a
  have d : (0 : ℚ)≤defect F := Nat.cast_nonneg _
  have lim := survivors F
  let good := ((shortBad F∪lateBad F)ᶜ).card
  let bad := (shortBad F).card+(lateBad F).card
  apply winners_of_loss bad good (by change _+(_+_)=_; rw [←Nat.add_assoc]; exact lim)
  change (((shortBad F).card+(lateBad F).card : Nat) : ℚ)/_≤_
  push_cast
  norm_num [ways,Nat.choose_eq_fast_choose,Nat.fast_choose,Nat.factorial,Thirty.triples,longMass,longPrice,lossCap] at long ⊢
  linarith only [s,long,d]

theorem exact_of_long (g : Coloring 30 29) (long : ((lateBad (coloringFactor g)).card : ℚ)/(ways 10 : ℚ)≤
    longMass*(longPrice+(defect (coloringFactor g) : ℚ)/18000)) : Exact g 20 :=
  of_positive g ((by decide : 0<2211739995828567).trans_le (winning_count_of_long _ long))

theorem exact_of_many_duplicates (g : Coloring 30 29) (dup : 1860≤defect (coloringFactor g)) : Exact g 20 := by
  classical
  let F : Factor V C := coloringFactor g
  have per (S : Finset V) (h : S∈cuts F (Fin.last 29) 10 4) :
      (noSix F univ∩localSeal univ S).card≤(ways 4-saving false 6 4)*(ways 6-saving false 9 6) := by
    obtain ⟨c,hc⟩ := side_mem.mp h
    obtain ⟨_,sz,cl⟩ := candidate_mem.mp hc
    exact long_noSix F S c (by simpa using cl) 4 6 sz (by rw [card_compl,Fintype.card_fin,sz]) (by decide) (by decide)
  have total := card_biUnion_le.trans (sum_le_sum per)
  rw [sum_const,nsmul_eq_mul] at total
  have cap := pure_global F (Fin.last 29) 10 4 30 (by simp) (by simp)
  have late := total.trans (Nat.mul_le_mul_right _ cap)
  have lateCount : (lateBad F).card≤pureTotal 30 10 4*((ways 4-saving false 6 4)*(ways 6-saving false 9 6)) := by unfold lateBad; exact late
  norm_num [pureTotal,saving,sixWeight,sixOverlap,ways,Nat.choose_eq_fast_choose,Nat.fast_choose,Nat.factorial] at lateCount
  have short := short_affine F
  have cnt := survivors F
  change _=1208883745669600000 at cnt
  change 1860≤defect F at dup
  apply of_positive
  change 0<((shortBad F∪lateBad F)ᶜ).card
  omega

#print axioms short_affine
#print axioms winning_count_of_long
#print axioms exact_of_many_duplicates

end WildSieve.Thirty.Graph
