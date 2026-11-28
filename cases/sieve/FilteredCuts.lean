import RegionLayouts
import OverlapCredit

namespace WildSieve.FilteredCuts
open Finset
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Count only layouts whose blocks avoid H and stay on one side of each prescribed cut. -/
noncomputable def layouts (H X : Finset (Finset V)) (U : Finset V) : Finset (Layout U) := by
  classical exact univ.filter fun D => ∀ b∈D.val,b∉H ∧ ∀ S∈X,b⊆S ∨ Disjoint b S

theorem mem_layouts {H X : Finset (Finset V)} {U : Finset V} {D : Layout U} :
    D∈layouts H X U ↔ ∀ b∈D.val,b∉H ∧ ∀ S∈X,b⊆S ∨ Disjoint b S := by
  classical simp [layouts]

private theorem side_iff {S U : Finset V} (D : Layout U) :
    D∈localSeal U (U∩S) ↔ ∀ b∈D.val,b⊆S ∨ Disjoint b S := by
  rw [seal_whole inter_subset_left]
  constructor
  · intro h b hb
    by_cases d : Disjoint b S
    · exact Or.inr d
    obtain ⟨v,vb,vs⟩ := not_disjoint_iff.mp d
    exact Or.inl ((h b hb v vb (mem_inter.mpr ⟨D.property.2 ▸ block_sub hb vb,vs⟩)).trans inter_subset_right)
  · intro h b hb x hx hs y hy
    rcases h b hb with inc|dis
    · exact mem_inter.mpr ⟨D.property.2 ▸ block_sub hb hy,inc hy⟩
    · exact False.elim (disjoint_left.mp dis hx (mem_inter.mp hs).2)

theorem insert_cut (H X : Finset (Finset V)) (U S : Finset V) :
    layouts H (insert S X) U = layouts H X U ∩ localSeal U (U∩S) := by
  classical
  ext D
  rw [mem_inter,mem_layouts,mem_layouts,side_iff]
  constructor
  · intro h
    exact ⟨fun b hb => ⟨(h b hb).1,fun T hT => (h b hb).2 T (mem_insert_of_mem hT)⟩,
      fun b hb => (h b hb).2 S (mem_insert_self ..)⟩
  · rintro ⟨old,new⟩ b hb
    exact ⟨(old b hb).1,fun T hT => (mem_insert.mp hT).elim (fun eq => eq ▸ new b hb) ((old b hb).2 T)⟩

/-- A mixed intersection of cut events factors exactly, including the exclusions H. -/
theorem count_insert (H X : Finset (Finset V)) (U S : Finset V) :
    (layouts H (insert S X) U).card = (layouts H X (U∩S)).card*(layouts H X (U \ S)).card := by
  classical
  let L := U∩S
  have sub : L⊆U := inter_subset_left
  have right : U \ L=U \ S := by ext v; simp [L]
  rw [←right]
  apply split_card U L sub _ _ _
  · rw [insert_cut]; exact inter_subset_right
  · intro P
    rw [insert_cut,mem_inter]
    have whole := seal_glue U L sub P
    change _ ∧ glueParts U L sub P∈localSeal U L ↔ _
    simp only [whole,and_true,mem_layouts]
    change (∀ b∈P.1.val∪P.2.val,_) ↔ _
    simp only [forall_mem_union]

/-- A count of a one- or two-cut intersection needs just the counts on its cells. -/
noncomputable def count (H : Finset (Finset V)) (U : Finset V) : List (Finset V) → Nat
  | [] => (layouts H ∅ U).card
  | S::rest => count H (U∩S) rest * count H (U \ S) rest

theorem count_eq (H : Finset (Finset V)) (U : Finset V) (cuts : List (Finset V)) :
    count H U cuts=(layouts H cuts.toFinset U).card := by
  induction cuts generalizing U with
  | nil => rfl
  | cons S rest ih => simp only [count,List.toFinset_cons,count_insert,ih]

end WildSieve.FilteredCuts
