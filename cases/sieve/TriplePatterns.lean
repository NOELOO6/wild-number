import TripleNeighbors

namespace WildSieve.SixCounts
open Finset
variable {n k : Nat}
local notation "V" => Fin n
local notation "C" => Fin k
local instance (priority := 2000) patternsEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq

/-- Both blocks in a particular splitting of a marked six. -/
noncomputable def splits (S : Finset V) : Finset (Blocks V) :=
  (univ : Finset (Layout S)).image Subtype.val
noncomputable def patterns (F : Factor V C) (U : Finset V) := (marks F U).biUnion splits

theorem split_mem {M : Blocks V} {S : Finset V} : M∈splits S ↔ Triples M ∧ vertices M=S := by
  classical
  constructor
  · intro h
    obtain ⟨L,_,rfl⟩ := mem_image.mp h
    exact L.property
  · intro h
    exact mem_image.mpr ⟨⟨M,h⟩,mem_univ _,rfl⟩

theorem pattern_mem {F : Factor V C} {U : Finset V} {M : Blocks V} : M∈patterns F U ↔
    Triples M ∧ vertices M∈marks F U := by
  classical
  constructor
  · intro h
    obtain ⟨S,hs,hm⟩ := mem_biUnion.mp h
    obtain ⟨ok,eq⟩ := split_mem.mp hm
    exact ⟨ok,eq.symm ▸ hs⟩
  · rintro ⟨ok,hs⟩
    exact mem_biUnion.mpr ⟨vertices M,hs,split_mem.mpr ⟨ok,rfl⟩⟩

theorem pattern_size {F : Factor V C} {U : Finset V} {M : Blocks V} (h : M∈patterns F U) : M.card=2 := by
  obtain ⟨ok,mark⟩ := pattern_mem.mp h
  have six := (mark_mem.mp mark).2.1
  have q := ok.card_vertices
  omega

theorem pattern_filter (F : Factor V C) (U : Finset V) :
    patterns F U=(patterns F univ).filter (fun M => vertices M⊆U) := by
  classical
  ext M
  simp only [mem_filter,pattern_mem,mark_mem,subset_univ,true_and]
  tauto

theorem weight_patterns (F : Factor V C) (U : Finset V) (f : Finset V → Nat) :
    (∑ M∈patterns F U,f (vertices M))=10*∑ S∈marks F U,f S := by
  classical
  have apart : ((marks F U) : Set (Finset V)).PairwiseDisjoint splits := by
    intro S _ T _ ne
    exact disjoint_left.mpr (fun _ hs ht => ne ((split_mem.mp hs).2.symm.trans (split_mem.mp ht).2))
  have each (S : Finset V) (h : S∈marks F U) : (∑ M∈splits S,f (vertices M))=10*f S := by
    have sz : (splits S).card=10 := by
      rw [splits,card_image_of_injective _ Subtype.val_injective,card_univ,card_layout 2 S (mark_mem.mp h).2.1]
      decide
    rw [sum_congr rfl (fun M hm => congrArg f (split_mem.mp hm).2),sum_const,sz,nsmul_eq_mul]
    rfl
  rw [patterns,sum_biUnion apart,sum_congr rfl each,mul_sum]

theorem pattern_card (F : Factor V C) (U : Finset V) : (patterns F U).card=10*(marks F U).card := by
  simpa using weight_patterns F U (fun _ => 1)

theorem pair_pattern {F : Factor V C} {A B : Finset V} (a : A.card=3) (hb : B∈neighbors F A) :
    ({A,B} : Blocks V)∈patterns F univ := by
  obtain ⟨sub,b,proper⟩ := neigh_mem.mp hb
  have sep : Disjoint A B := disjoint_left.mpr fun _ ha h => mem_compl.mp (sub h) ha
  have eq : vertices ({A,B} : Blocks V)=A∪B := by ext x; simp [vertices]
  apply pattern_mem.mpr
  constructor
  · constructor
    · intro Z h; simp only [mem_insert,mem_singleton] at h; rcases h with rfl|rfl <;> assumption
    · intro X x Y y ne
      simp only [mem_insert,mem_singleton] at x y
      rcases x with rfl|rfl <;> rcases y with rfl|rfl <;> first | exact (ne rfl).elim | exact sep | exact sep.symm
  · rw [eq]
    exact mark_mem.mpr ⟨subset_univ _,by rw [card_union_of_disjoint sep,a,b],proper⟩

/-- The other block of a two-block pattern is a neighbor of the first. -/
theorem other_neighbor {F : Factor V C} {U : Finset V} {A B : Finset V}
    (ne : A≠B) (h : ({A,B} : Blocks V)∈patterns F U) : B∈neighbors F A := by
  obtain ⟨ok,mark⟩ := pattern_mem.mp h
  have a : A∈({A,B} : Blocks V) := by simp
  have b : B∈({A,B} : Blocks V) := by simp
  have sep := ok.separate _ a _ b ne
  obtain ⟨_,_,c,cl⟩ := mark_mem.mp mark
  refine neigh_mem.mpr ⟨fun x hx => mem_compl.mpr (fun h => disjoint_left.mp sep h hx),ok.size _ b,c,?_⟩
  simpa [vertices] using cl

theorem supports_disjoint {M J : Blocks V} (parts : Triples (M∪J)) (d : Disjoint M J) :
    Disjoint (vertices M) (vertices J) := by
  apply disjoint_left.mpr
  intro x hm hj
  obtain ⟨A,ha,ax⟩ := mem_biUnion.mp hm
  obtain ⟨B,hb,bx⟩ := mem_biUnion.mp hj
  have eq := parts.only (mem_union_left _ ha) (mem_union_right _ hb) ax bx
  exact disjoint_left.mp d (eq ▸ ha) hb

theorem blocks_disjoint {M J : Blocks V} (parts : Triples M) (d : Disjoint (vertices M) (vertices J)) :
    Disjoint M J := by
  apply disjoint_left.mpr
  intro A ha hb
  obtain ⟨x,hx⟩ := card_pos.mp (show 0<A.card by rw [parts.size _ ha]; decide)
  exact disjoint_left.mp d (block_sub ha hx) (block_sub hb hx)

end WildSieve.SixCounts
