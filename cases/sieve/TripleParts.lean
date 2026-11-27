import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Powerset

namespace WildSieve
open Finset
variable {V : Type} [DecidableEq V]

abbrev Blocks (V : Type) := Finset (Finset V)
def vertices (D : Blocks V) := D.biUnion id

structure Triples (D : Blocks V) : Prop where
  size : ∀ b ∈ D, b.card = 3
  separate : ∀ a ∈ D, ∀ b ∈ D, a ≠ b → Disjoint a b

theorem block_sub {D : Blocks V} {b : Finset V} (h : b ∈ D) : b ⊆ vertices D :=
  fun _ hv => mem_biUnion.mpr ⟨b,h,hv⟩

omit [DecidableEq V] in
theorem Triples.only {D : Blocks V} (h : Triples D) {a b : Finset V}
    (ha : a ∈ D) (hb : b ∈ D) {v : V} (va : v ∈ a) (vb : v ∈ b) : a=b := by
  by_contra ne
  exact disjoint_left.mp (h.separate _ ha _ hb ne) va vb

theorem Triples.card_vertices {D : Blocks V} (h : Triples D) : (vertices D).card = 3*D.card := by
  have dis : (D : Set (Finset V)).PairwiseDisjoint id := fun _ ha _ hb ne => h.separate _ ha _ hb ne
  rw [vertices,Finset.card_biUnion dis]
  calc
    ∑ b ∈ D,(id b).card = ∑ _ ∈ D,3 := sum_congr rfl (fun b hb => h.size b hb)
    _ = _ := by simp [Nat.mul_comm]

omit [DecidableEq V] in
theorem Triples.sub {D M : Blocks V} (h : Triples D) (sub : M ⊆ D) : Triples M :=
  ⟨fun a ha => h.size a (sub ha),fun a ha b hb => h.separate a (sub ha) b (sub hb)⟩

theorem Triples.combine {D M : Blocks V} (h : Triples D) (k : Triples M)
    (dis : Disjoint (vertices D) (vertices M)) : Triples (D ∪ M) := by
  refine ⟨?_,?_⟩
  · intro b hb
    rcases mem_union.mp hb with u|u
    · exact h.size _ u
    · exact k.size _ u
  · intro a ha b hb ne
    rcases mem_union.mp ha with ha|ha <;> rcases mem_union.mp hb with hb|hb
    · exact h.separate _ ha _ hb ne
    · exact dis.mono (block_sub ha) (block_sub hb)
    · exact dis.symm.mono (block_sub ha) (block_sub hb)
    · exact k.separate _ ha _ hb ne

@[simp] theorem vertices_union (D M : Blocks V) : vertices (D ∪ M) = vertices D ∪ vertices M := by
  classical
  ext v
  simp [vertices,exists_or,or_and_right]

theorem Triples.remove {D M : Blocks V} (h : Triples D) (sub : M ⊆ D) :
    vertices (D \ M) = vertices D \ vertices M := by
  ext v
  constructor
  · intro hv
    obtain ⟨b,hb,vb⟩ := mem_biUnion.mp hv
    obtain ⟨bd,bm⟩ := mem_sdiff.mp hb
    refine mem_sdiff.mpr ⟨block_sub bd vb,?_⟩
    rintro vm
    obtain ⟨a,am,va⟩ := mem_biUnion.mp vm
    exact bm ((h.only bd (sub am) vb va).symm ▸ am)
  · intro hv
    obtain ⟨vd,vm⟩ := mem_sdiff.mp hv
    obtain ⟨b,bd,vb⟩ := mem_biUnion.mp vd
    exact mem_biUnion.mpr ⟨b,mem_sdiff.mpr ⟨bd,fun bm => vm (block_sub bm vb)⟩,vb⟩

abbrev Layout (S : Finset V) := {D : Blocks V // Triples D ∧ vertices D = S}

noncomputable instance [Fintype V] (S : Finset V) : Fintype (Layout S) := by
  classical
  exact Fintype.ofFinite _

/-- Removing or adjoining specified whole triples is a bijection on completions. -/
noncomputable def completeEquiv (S : Finset V) (M : Blocks V) (h : Triples M)
    (inside : vertices M ⊆ S) : {D : Layout S // M ⊆ D.val} ≃ Layout (S \ vertices M) := by
  classical
  let remove (D : {D : Layout S // M ⊆ D.val}) : Layout (S \ vertices M) :=
    ⟨D.val.val \ M,D.val.property.1.sub sdiff_subset,by rw [D.val.property.1.remove D.property,D.val.property.2]⟩
  have dis (L : Layout (S \ vertices M)) : Disjoint (vertices M) (vertices L.val) := by
    rw [L.property.2]
    exact disjoint_sdiff
  let add (L : Layout (S \ vertices M)) : {D : Layout S // M ⊆ D.val} :=
    ⟨⟨M ∪ L.val,h.combine L.property.1 (dis L),by rw [vertices_union,L.property.2,union_sdiff_of_subset inside]⟩,
      subset_union_left⟩
  refine ⟨remove,add,?_,?_⟩
  · intro D
    apply Subtype.ext
    apply Subtype.ext
    exact union_sdiff_of_subset D.property
  · intro L
    apply Subtype.ext
    change (M ∪ L.val) \ M = L.val
    ext b
    have both (bm : b ∈ M) (bl : b ∈ L.val) : False := by
      obtain ⟨v,hv⟩ := card_pos.mp (by rw [h.size b bm]; decide)
      exact disjoint_left.mp (dis L) (block_sub bm hv) (block_sub bl hv)
    simp only [mem_sdiff,mem_union]
    exact ⟨fun ⟨x,n⟩ => x.resolve_left n,fun bl => ⟨Or.inr bl,fun bm => both bm bl⟩⟩

/-- The recurrence counts partitions of 3k labeled points into unordered triples. -/
def ways : Nat → Nat
  | 0 => 1
  | k+1 => Nat.fast_choose (3*k+2) 2 * ways k

theorem ways_pos (k : Nat) : 0 < ways k := by
  induction k with
  | zero => decide
  | succ k ih =>
    simp only [ways,← Nat.choose_eq_fast_choose]
    exact Nat.mul_pos (Nat.choose_pos (by omega)) ih

end WildSieve
