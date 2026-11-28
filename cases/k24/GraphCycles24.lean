import MatchingCycles
import CycleData24
import SixCounts

namespace WildSieve.TwentyFour
open Finset WildExact WildAnchor WildAnchor.Alternating
local instance (priority := 2000) cycleEq {n : Nat} : DecidableEq (Fin n) := (inferInstance : LinearOrder (Fin n)).toDecidableEq

/-- Internal matching edges in a bipartite chart of the union of two colors. -/
def pairedIndices {m : Nat} (p : Equiv.Perm (Fin m)) (S : Finset (Point m)) :=
  (univ : Finset (Fin m)).filter fun i => (i,false)∈S ∧ (p i,true)∈S

theorem inside_chart {n m : Nat} (g : Coloring (n+1) n) (c : Fin n) (w : Point m ≃ Fin (n+1))
    (p : Equiv.Perm (Fin m)) (paint : ∀ i,g.paint (w (i,false)) (w (p i,true))=c)
    (S : Finset (Point m)) :
    Inside (coloringFactor g) c (S.map w.toEmbedding)=(pairedIndices p S).card := by
  classical
  let a (i : Fin m) := w (i,false)
  let b (i : Fin m) := w (p i,true)
  have ne (i t) : a i≠b t := fun eq => Bool.noConfusion (congrArg Prod.snd (w.injective eq))
  have forward (i) : mate g c (a i)=b i :=
    g.proper _ _ _ (mate_spec g c _).1 (ne i i) ((mate_spec g c _).2.trans (paint i).symm)
  have reverse (i) : mate g c (b i)=a i := forward i ▸ mate_involutive g c (a i)
  let lower (i : Fin m) := min (a i) (b i)
  have ai : Function.Injective a := fun _ _ eq => congrArg Prod.fst (w.injective eq)
  have bi : Function.Injective b := fun _ _ eq => p.injective (congrArg Prod.fst (w.injective eq))
  have uniq : Function.Injective lower := by
    intro i t eq
    dsimp only [lower] at eq
    rcases le_total (a i) (b i) with h|h <;> rcases le_total (a t) (b t) with k|k
    · exact ai (by simpa [min_eq_left h,min_eq_left k] using eq)
    · exact False.elim (ne _ _ (by simpa [min_eq_left h,min_eq_right k] using eq))
    · exact False.elim (ne _ _ (by simpa [min_eq_right h,min_eq_left k] using eq.symm))
    · exact bi (by simpa [min_eq_right h,min_eq_right k] using eq)
  have aw (i) : a i∈S.map w.toEmbedding ↔ (i,false)∈S := by simp [a]
  have bw (i) : b i∈S.map w.toEmbedding ↔ (p i,true)∈S := by simp [b]
  symm
  apply card_bij (fun i _ => lower i)
  · intro i hi
    obtain ⟨x,y⟩ := (mem_filter.mp hi).2
    change lower i∈lowerEnds (mate g c) _
    rcases lt_or_gt_of_ne (ne i i) with h|h
    · rw [show lower i=a i from min_eq_left h.le]
      exact mem_filter.mpr ⟨(aw i).mpr x,forward i ▸ h,forward i ▸ (bw i).mpr y⟩
    · rw [show lower i=b i from min_eq_right h.le]
      exact mem_filter.mpr ⟨(bw i).mpr y,reverse i ▸ h,reverse i ▸ (aw i).mpr x⟩
  · exact fun _ _ _ _ eq => uniq eq
  · intro v hv
    change v∈lowerEnds (mate g c) _ at hv
    obtain ⟨x,lt,y⟩ := mem_filter.mp hv
    obtain ⟨⟨i,bit⟩,rfl⟩ := w.surjective v
    cases bit
    · change a i<mate g c (a i) at lt
      rw [forward] at lt
      have yy : b i∈S.map w.toEmbedding := forward i ▸ y
      exact ⟨i,mem_filter.mpr ⟨mem_univ _,(aw i).mp x,(bw i).mp yy⟩,min_eq_left lt.le⟩
    · let t := p.symm i
      have point : b t=w (i,true) := by simp [b,t]
      rw [←point] at x lt y ⊢
      rw [reverse] at lt y
      exact ⟨t,mem_filter.mpr ⟨mem_univ _,(aw t).mp y,(bw t).mp x⟩,min_eq_right lt.le⟩

private theorem convention : (WildAnchor.cycleLists 12 2 12).all (fun cs =>
    (List.finRange 12).all fun i => ((cyclePerm 12 cs) i).val==successor cs i.val)=true := by native_decide

private theorem same_shapes : WildAnchor.cycleLists 12 2 12=shapes := by native_decide

/-- Every distinct pair of actual colors has one of the 21 shapes used by the
certificate, with the correct internal-edge counts on every vertex subset. -/
theorem chart_of_colors (g : Coloring 24 23) (a c : Fin 23) (ne : c≠a) :
    ∃ cs∈shapes,∃ w : Point 12 ≃ Fin 24,∀ S : Finset (Point 12),
      Inside (coloringFactor g) a (S.map w.toEmbedding)=(pairedIndices (Equiv.refl _) S).card ∧
      Inside (coloringFactor g) c (S.map w.toEmbedding)=(pairedIndices (cyclePerm 12 cs) S).card := by
  obtain ⟨cs,ordered,w,first,second⟩ := charts_of_periods g a c (m:=12) (by decide) 2
    (by decide) (min_two g a c ne) convention
  refine ⟨cs,same_shapes ▸ WildAnchor.cycle_member (by decide : 0<2) ordered,w,fun S =>
    ⟨inside_chart g a w _ first S,inside_chart g c w _ second S⟩⟩

#print axioms chart_of_colors
end WildSieve.TwentyFour
