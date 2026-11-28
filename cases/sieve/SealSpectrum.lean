import LayoutSplit

namespace WildSieve
open Finset
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Number of triple layouts on a set of n points, including impossible sizes. -/
def layoutWays (n : Nat) := if n%3=0 then ways (n/3) else 0

theorem card_layout_all (U : Finset V) : Fintype.card (Layout U)=layoutWays U.card := by
  by_cases h : U.card%3=0
  · exact (card_layout (U.card/3) U (by omega)).trans (by simp [layoutWays,h])
  · rw [layoutWays,if_neg h,Fintype.card_eq_zero_iff]
    refine ⟨fun D => ?_⟩
    have size := D.property.1.card_vertices
    rw [D.property.2] at size
    omega

def sealWays (n k : Nat) := layoutWays k*layoutWays (n-k)

theorem local_seal_ways (X Y : Finset V) (sub : Y⊆X) :
    (localSeal X Y).card=sealWays X.card Y.card := by
  classical
  let full := @Finset.univ (Layout (X \ Y)) _
  have count := drop_cut X Y sub (localSeal X Y) full (fun _ h => h)
    (fun P => by simp [full,seal_glue])
  simpa [full,sealWays,card_layout_all,card_sdiff sub] using count

theorem seal_glue_both (X L S : Finset V) (lx : L⊆X) (sx : S⊆X)
    (P : Layout L × Layout (X \ L)) :
    glueParts X L lx P∈localSeal X S ↔
      P.1∈localSeal L (S∩L) ∧ P.2∈localSeal (X \ L) (S \ L) := by
  have away : S \ L ⊆ X \ L := fun _ h => mem_sdiff.mpr ⟨sx (mem_sdiff.mp h).1,(mem_sdiff.mp h).2⟩
  constructor
  · intro sealed
    have parts := seal_parts (seal_glue X L lx P) sealed
    have left := (seal_glue_left X L (L∩S) lx P inter_subset_left).mp parts.1
    exact ⟨inter_comm L S ▸ left,(seal_glue_right X L _ lx P away).mp parts.2⟩
  · rintro ⟨left,right⟩
    obtain ⟨A,ha⟩ := local_seal_mem.mp left
    obtain ⟨B,hb⟩ := local_seal_mem.mp right
    have dis : Disjoint (vertices A.val) (vertices B.val) := by
      rw [A.property.2,B.property.2]
      exact disjoint_left.mpr (fun _ hi hd => (mem_sdiff.mp hd).2 (mem_inter.mp hi).2)
    apply local_seal_mem.mpr
    refine ⟨⟨A.val∪B.val,A.property.1.combine B.property.1 dis,?_⟩,union_subset_union ha hb⟩
    rw [vertices_union,A.property.2,B.property.2]
    ext v
    simp only [mem_union,mem_inter,mem_sdiff]
    tauto

/-- Exact joint count for arbitrary overlapping cuts. Each cell of the
two-set Venn diagram must itself be partitioned into triples. -/
theorem joint_seal_ways (X L S : Finset V) (lx : L⊆X) (sx : S⊆X) :
    (localSeal X L ∩ localSeal X S).card=
      sealWays L.card (S∩L).card * sealWays (X \ L).card (S \ L).card := by
  rw [split_card X L lx _ (localSeal L (S∩L)) (localSeal (X \ L) (S \ L)) inter_subset_left (fun P => by
    rw [mem_inter,seal_glue_both X L S lx sx P]
    simp [seal_glue])]
  rw [local_seal_ways _ _ inter_subset_right,local_seal_ways _ _ (fun _ h => mem_sdiff.mpr ⟨sx (mem_sdiff.mp h).1,(mem_sdiff.mp h).2⟩)]

end WildSieve
