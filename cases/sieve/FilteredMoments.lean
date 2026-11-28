import FilteredCuts

namespace WildSieve.FilteredCuts
open Finset
variable {V : Type} [Fintype V] [DecidableEq V]

theorem layouts_inter (H X Y : Finset (Finset V)) (U : Finset V) :
    layouts H X U ∩ layouts H Y U=layouts H (X∪Y) U := by
  ext D
  simp only [mem_inter,mem_layouts,forall_mem_union]
  constructor
  · rintro ⟨p,q⟩ b hb; exact ⟨(p b hb).1,(p b hb).2,(q b hb).2⟩
  · intro h; exact ⟨fun b hb => ⟨(h b hb).1,(h b hb).2.1⟩,fun b hb => ⟨(h b hb).1,(h b hb).2.2⟩⟩

noncomputable def survivors (H K : Finset (Finset V)) (U : Finset V) :=
  layouts H ∅ U \ K.biUnion (fun S => layouts H {S} U)

noncomputable def first (H K : Finset (Finset V)) (U : Finset V) :=
  ∑ S∈K,count H U [S]
noncomputable def second (H K : Finset (Finset V)) (U : Finset V) :=
  ∑ S∈K,∑ T∈K.erase S,count H U [S,T]
noncomputable def third (H K : Finset (Finset V)) (U : Finset V) :=
  ∑ S∈K,∑ T∈K.erase S,∑ R∈(K.erase S).erase T,count H U [S,T,R]

private theorem lost_sub (H K : Finset (Finset V)) (U : Finset V) :
    K.biUnion (fun S => layouts H {S} U)⊆layouts H ∅ U := by
  intro D h
  obtain ⟨S,_,a⟩ := mem_biUnion.mp h
  exact mem_layouts.mpr (fun b hb => ⟨(mem_layouts.mp a b hb).1,by simp⟩)

private theorem two (H : Finset (Finset V)) (U S T : Finset V) :
    (layouts H {S} U∩layouts H {T} U).card=count H U [S,T] := by
  simp [count_eq,layouts_inter]
  congr 2

private theorem three (H : Finset (Finset V)) (U S T R : Finset V) :
    (layouts H {S} U∩layouts H {T} U∩layouts H {R} U).card=count H U [S,T,R] := by
  simp [count_eq,layouts_inter,insert_union]
  congr 2

/-- Ordered intersections at the second and third levels retain any exclusion on individual triples. -/
theorem cubic (H K : Finset (Finset V)) (U : Finset V) :
    6*count H U []+3*second H K U ≤ 6*(survivors H K U).card+6*first H K U+third H K U := by
  classical
  have credit := overlap_credit K (fun S => layouts H {S} U) (fun S => K.erase S) (fun _ _ => Subset.rfl)
  simp_rw [two,three] at credit
  have single (S : Finset V) : (layouts H {S} U).card=count H U [S] := by simp [count_eq]
  simp_rw [single] at credit
  have total := card_sdiff_add_card_eq_card (lost_sub H K U)
  change (survivors H K U).card+_= (layouts H ∅ U).card at total
  unfold count first second third
  omega

/-- The stronger cubic with zeros at one, three and four hits. -/
theorem cubic_twelve (H K : Finset (Finset V)) (U : Finset V) :
    12*count H U []+5*second H K U ≤ 12*(survivors H K U).card+12*first H K U+third H K U := by
  classical
  have credit := overlap_credit_twelve K (fun S => layouts H {S} U) (fun S => K.erase S) (fun _ _ => Subset.rfl)
  simp_rw [two,three] at credit
  have single (S : Finset V) : (layouts H {S} U).card=count H U [S] := by simp [count_eq]
  simp_rw [single] at credit
  have total := card_sdiff_add_card_eq_card (lost_sub H K U)
  change (survivors H K U).card+_= (layouts H ∅ U).card at total
  unfold count first second third
  omega

end WildSieve.FilteredCuts
