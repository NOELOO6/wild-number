import ExteriorPorts
import FiveTriples
namespace WildExterior
open Finset WildSieve

/-- The two triples on the six vertices outside the nine labeled points and
the fixed root. -/
structure Split (i : Port ↪ V) (A B : Finset V) : Prop where
  a : A.card=3
  b : B.card=3
  apart : Disjoint A B
  inside : A∪B=(outside i)ᶜ.erase root

def outsideBlocks (i : Port ↪ V) (L : Layout (univ : Finset Port)) := L.val.image (map i)
def allBlocks (i : Port ↪ V) (A B : Finset V) (L : Layout (univ : Finset Port)) :=
  (({A}:Blocks V)∪{B})∪outsideBlocks i L

theorem outside_blocks (i : Port ↪ V) (L : Layout (univ : Finset Port)) :
    Triples (outsideBlocks i L) ∧ vertices (outsideBlocks i L)=outside i := by
  constructor
  · constructor
    · intro T ht
      obtain ⟨t,ht₀,rfl⟩ := mem_image.mp ht
      rw [card_map,L.property.1.size t ht₀]
    · intro T ht U hu ne
      obtain ⟨t,ht₀,rfl⟩ := mem_image.mp ht
      obtain ⟨u,hu₀,rfl⟩ := mem_image.mp hu
      exact (disjoint_map i).mpr (L.property.1.separate t ht₀ u hu₀ (fun eq => ne (eq ▸ rfl)))
  · ext v
    constructor
    · intro h
      obtain ⟨T,ht,vt⟩ := mem_biUnion.mp h
      obtain ⟨t,_,rfl⟩ := mem_image.mp ht
      obtain ⟨x,_,eq⟩ := mem_map.mp vt
      exact outside_mem.mpr ⟨x,eq⟩
    · intro h
      obtain ⟨x,rfl⟩ := outside_mem.mp h
      have mem : x∈vertices L.val := by rw [L.property.2];simp
      obtain ⟨t,ht,xt⟩ := mem_biUnion.mp mem
      exact mem_biUnion.mpr ⟨t.map i,mem_image.mpr ⟨t,ht,rfl⟩,mem_map.mpr ⟨x,xt,rfl⟩⟩

theorem split_layout {i : Port ↪ V} {A B : Finset V} (s : Split i A B) (out : root∉outside i)
    (L : Layout (univ : Finset Port)) :
    Triples (allBlocks i A B L) ∧ vertices (allBlocks i A B L)=univ.erase root := by
  obtain ⟨tri,vert⟩ := outside_blocks i L
  have inside := (singleton_triple s.a).combine (singleton_triple s.b) (by simpa using s.apart)
  have apart : Disjoint (A∪B) (outside i) := by
    rw [s.inside]
    exact disjoint_compl_left.mono_left (erase_subset _ _)
  constructor
  · exact inside.combine tri (by simpa only [vertices_union,vertices_singleton,vert] using apart)
  · simp only [allBlocks,vertices_union,vertices_singleton,vert,s.inside]
    ext x
    by_cases h : x=root
    · subst x;simp [out]
    · simp [h];tauto

theorem all_mem {i : Port ↪ V} {A B T : Finset V} {L : Layout (univ : Finset Port)} :
    T∈allBlocks i A B L ↔ T=A ∨ T=B ∨ ∃ t∈L.val,t.map i=T := by
  simp [allBlocks,outsideBlocks,or_assoc]

theorem other_six (i : Port ↪ V) (L : Layout (univ : Finset Port)) (a b : Finset Port)
    (ha : a∈L.val) (hb : b∈L.val) (ne : a≠b) :
    ∃ t∈L.val,a.map i ∪ b.map i=outside i \ t.map i := by
  have sz := L.property.1.card_vertices
  rw [L.property.2,card_univ,Fintype.card_fin] at sz
  let M : Blocks Port := {a,b}
  have sub : M⊆L.val := by
    intro t ht
    rcases mem_insert.mp ht with rfl|h
    · exact ha
    · exact mem_singleton.mp h ▸ hb
  have cnt : (L.val \ M).card=1 := by
    have sum := card_sdiff_add_card_eq_card sub
    have ms : M.card=2 := by simp [M,ne]
    omega
  obtain ⟨t,eq⟩ := card_eq_one.mp cnt
  have ht := mem_sdiff.mp (show t∈L.val \ M from eq ▸ mem_singleton_self _)
  have left := L.property.1.remove sub
  rw [eq,vertices_singleton,L.property.2] at left
  have teq : t=(a∪b)ᶜ := by
    change t=univ \ (a∪b)
    simpa [M,vertices] using left
  have tt : a∪b=tᶜ := by rw [teq,compl_compl]
  refine ⟨t,ht.1,?_⟩
  rw [←map_union,tt]
  ext v
  simp only [outside,mem_map,mem_compl,mem_sdiff,mem_univ,true_and]
  constructor
  · rintro ⟨x,nx,rfl⟩
    exact ⟨⟨x,rfl⟩,fun ⟨y,hm,eq⟩ => nx (i.injective eq ▸ hm)⟩
  · rintro ⟨⟨x,rfl⟩,hn⟩
    exact ⟨x,fun h => hn ⟨x,h,rfl⟩,rfl⟩

theorem inside_six_open (F : Factor V Color) (i : Port ↪ V) {A B : Finset V}
    (s : Split i A B) (rule : ∀ c,Inside F c (outside i)ᶜ≤2) (c : Color) : ¬Closed (F.f c) (A∪B) := by
  intro cl
  have count := closed_size (F.invol c) (F.moving c) cl
  have size : (A∪B).card=6 := by rw [card_union_of_disjoint s.apart,s.a,s.b]
  have sub : A∪B⊆(outside i)ᶜ := s.inside ▸ erase_subset _ _
  have cap := (inside_mono F c sub).trans (rule c)
  change (lowerEnds (F.f c) (A∪B)).card≤2 at cap
  omega
end WildExterior
