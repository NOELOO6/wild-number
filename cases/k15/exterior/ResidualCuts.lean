import ExteriorSplit
import ExteriorCuts
namespace WildExterior
open Finset WildSieve

/-- The remaining ways a color can get cut off all involve a specific
three-point half of the fixed six. -/
theorem residual_cuts (F : Factor V Color) (i : Port ↪ V) {A B : Finset V} (s : Split i A B)
    (rule : ∀ c,Inside F c (outside i)ᶜ≤2) (L : Layout (univ : Finset Port))
    (pass : ∀ t∈L.val,∀ c,¬Closed (F.f c) (insert root (t.map i)) ∧ ¬Closed (F.f c) (outside i \ t.map i))
    (c : Color) (Q : Finset V) (cl : Closed (F.f c) Q)
    (kind : (∃ T∈allBlocks i A B L,Q=insert root T) ∨
      (∃ T∈allBlocks i A B L,∃ U∈allBlocks i A B L,T≠U ∧ Q=T∪U)) :
    ∃ C,C∈({A,B}:Blocks V) ∧ (Q=insert root C ∨ ∃ t∈L.val,Q=C∪t.map i) := by
  classical
  rcases kind with ⟨T,ht,rfl⟩|⟨T,ht,U,hu,ne,rfl⟩
  · rcases all_mem.mp ht with rfl|rfl|⟨t,tx,rfl⟩
    · exact ⟨_,mem_insert_self _ _,Or.inl rfl⟩
    · exact ⟨_,mem_insert_of_mem (mem_singleton_self _),Or.inl rfl⟩
    · exact ((pass t tx c).1 cl).elim
  · rcases all_mem.mp ht with rfl|rfl|⟨t,tx,rfl⟩ <;>
      rcases all_mem.mp hu with rfl|rfl|⟨u,ux,rfl⟩
    · exact (ne rfl).elim
    · exact (inside_six_open F i s rule c cl).elim
    · exact ⟨_,mem_insert_self _ _,Or.inr ⟨u,ux,rfl⟩⟩
    · exact (inside_six_open F i s rule c (by simpa only [union_comm] using cl)).elim
    · exact (ne rfl).elim
    · exact ⟨_,mem_insert_of_mem (mem_singleton_self _),Or.inr ⟨u,ux,rfl⟩⟩
    · exact ⟨_,mem_insert_self _ _,Or.inr ⟨t,tx,union_comm _ _⟩⟩
    · exact ⟨_,mem_insert_of_mem (mem_singleton_self _),Or.inr ⟨t,tx,union_comm _ _⟩⟩
    · obtain ⟨z,hz,eq⟩ := other_six i L t u tx ux (fun eq => ne (eq ▸ rfl))
      exact ((pass z hz c).2 (eq ▸ cl)).elim

theorem split_exists (i : Port ↪ V) (out : root∉outside i) :
    ∃ A B : Finset V,Split i A B := by
  let H := (outside i)ᶜ.erase root
  have sz : H.card=6 := by rw [card_erase_of_mem (mem_compl.mpr out),seven]
  obtain ⟨A,sub,three⟩ := exists_subset_card_eq (show 3≤H.card by omega)
  have cnt := card_sdiff_add_card_eq_card sub
  exact ⟨A,H \ A,three,by omega,disjoint_sdiff,union_sdiff_of_subset sub⟩
end WildExterior
