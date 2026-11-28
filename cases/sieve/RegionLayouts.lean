import SealSpectrum
import Mathlib.Data.Fintype.BigOperators

namespace WildSieve
open Finset
variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

/-- A region is sealed precisely when every block meeting it is contained in it. -/
theorem seal_whole {X S : Finset V} (sub : S⊆X) (D : Layout X) :
    D∈localSeal X S ↔ ∀ b∈D.val,∀ v∈b,v∈S → b⊆S := by
  constructor
  · rintro hit b hb v vb vs
    obtain ⟨P,hp⟩ := local_seal_mem.mp hit
    obtain ⟨a,ha,va⟩ := mem_biUnion.mp (show v∈vertices P.val from P.property.2.symm ▸ vs)
    exact (D.property.1.only hb (hp ha) vb va).symm ▸ P.property.2 ▸ block_sub ha
  · intro whole
    let M := D.val.filter (·⊆S)
    have eq : vertices M=S := by
      ext v
      constructor
      · rintro h
        obtain ⟨b,hb,vb⟩ := mem_biUnion.mp h
        exact (mem_filter.mp hb).2 vb
      · intro vs
        obtain ⟨b,hb,vb⟩ := mem_biUnion.mp (D.property.2.symm ▸ sub vs)
        exact mem_biUnion.mpr ⟨b,mem_filter.mpr ⟨hb,whole b hb v vb vs⟩,vb⟩
    exact local_seal_mem.mpr ⟨⟨M,D.property.1.sub (filter_subset _ _),eq⟩,filter_subset _ _⟩

namespace Regions

def cell (z : V → I) (i : I) := (univ : Finset V).filter (fun v => z v=i)

omit [DecidableEq V] [Fintype I] in
theorem cell_mem {z : V → I} {i : I} {v : V} : v∈cell z i ↔ z v=i := by simp [cell]

abbrev Pieces (z : V → I) := ∀ i,Layout (cell z i)

omit [Fintype I] in
private theorem where_block {z : V → I} {P : Pieces z} {i : I} {b : Finset V}
    (hb : b∈(P i).val) : b⊆cell z i := (P i).property.2 ▸ block_sub hb

omit [Fintype I] in
private theorem block_index {z : V → I} {P T : Pieces z} {i j : I} {b : Finset V}
    (a : b∈(P i).val) (c : b∈(T j).val) : i=j := by
  obtain ⟨v,hv⟩ := card_pos.mp (show 0<b.card by rw [(P i).property.1.size b a]; decide)
  exact (cell_mem.mp (where_block a hv)).symm.trans (cell_mem.mp (where_block c hv))

noncomputable def assemble (z : V → I) : Pieces z ↪ Layout (univ : Finset V) where
  toFun P := ⟨univ.biUnion (fun i => (P i).val),by
    constructor
    · constructor
      · intro b hb
        obtain ⟨i,_,h⟩ := mem_biUnion.mp hb
        exact (P i).property.1.size b h
      · intro a ha b hb ne
        obtain ⟨i,_,ai⟩ := mem_biUnion.mp ha
        obtain ⟨j,_,bj⟩ := mem_biUnion.mp hb
        by_cases ij : i=j
        · subst j; exact (P i).property.1.separate a ai b bj ne
        · exact disjoint_left.mpr (fun v va vb => ij ((cell_mem.mp (where_block ai va)).symm.trans
            (cell_mem.mp (where_block bj vb))))
    · apply eq_univ_of_forall
      intro v
      have whereV : v∈vertices (P (z v)).val := (P _).property.2.symm ▸ cell_mem.mpr rfl
      obtain ⟨b,hb,vb⟩ := mem_biUnion.mp whereV
      exact mem_biUnion.mpr ⟨b,mem_biUnion.mpr ⟨_,mem_univ _,hb⟩,vb⟩⟩
  inj' := by
    intro P T same
    have eq : univ.biUnion (fun i => (P i).val)=univ.biUnion (fun i => (T i).val) :=
      congrArg Subtype.val same
    have incl (A B : Pieces z) (h : univ.biUnion (fun i => (A i).val)⊆univ.biUnion (fun i => (B i).val))
        (i : I) : (A i).val⊆(B i).val := by
      intro b hb
      obtain ⟨j,_,hj⟩ := mem_biUnion.mp (h (mem_biUnion.mpr ⟨i,mem_univ _,hb⟩))
      exact block_index hb hj ▸ hj
    funext i
    exact Subtype.ext (Subset.antisymm (incl P T (le_of_eq eq) i) (incl T P (le_of_eq eq.symm) i))

noncomputable def decks (z : V → I) := univ.map (assemble z)

theorem decks_mem {z : V → I} {D : Layout (univ : Finset V)} :
    D∈decks z ↔ ∀ i,D∈localSeal univ (cell z i) := by
  classical
  constructor
  · intro h i
    obtain ⟨P,_,rfl⟩ := mem_map.mp h
    exact local_seal_mem.mpr ⟨P i,fun _ hb => mem_biUnion.mpr ⟨i,mem_univ _,hb⟩⟩
  · intro h
    choose P hp using fun i => local_seal_mem.mp (h i)
    refine mem_map.mpr ⟨P,mem_univ _,Subtype.ext (Subset.antisymm (biUnion_subset.mpr (fun i _ => hp i)) ?_)⟩
    intro b hb
    obtain ⟨v,vb⟩ := card_pos.mp (show 0<b.card by rw [D.property.1.size b hb]; decide)
    have vi : v∈vertices (P (z v)).val := (P _).property.2.symm ▸ cell_mem.mpr rfl
    obtain ⟨a,ha,va⟩ := mem_biUnion.mp vi
    exact mem_biUnion.mpr ⟨z v,mem_univ _,(D.property.1.only hb (hp _ ha) vb va).symm ▸ ha⟩

theorem decks_constant (z : V → I) (D : Layout (univ : Finset V)) :
    D∈decks z ↔ ∀ b∈D.val,∀ v∈b,∀ w∈b,z v=z w := by
  rw [decks_mem]
  constructor
  · intro h b hb v hv w hw
    exact (cell_mem.mp ((seal_whole (subset_univ _) D).mp (h (z v)) b hb v hv (cell_mem.mpr rfl) hw)).symm
  · intro h i
    apply (seal_whole (subset_univ _) D).mpr
    intro b hb v hv vi w hw
    exact cell_mem.mpr ((h b hb w hw v hv).trans (cell_mem.mp vi))

theorem decks_card (z : V → I) : (decks z).card=∏ i,layoutWays (cell z i).card := by
  simp [decks,Fintype.card_pi,card_layout_all]

theorem assemble_seal (z : V → I) (P : Pieces z) (S : Finset V) :
    assemble z P∈localSeal univ S ↔ ∀ i,P i∈localSeal (cell z i) (S∩cell z i) := by
  rw [seal_whole (subset_univ _)]
  constructor
  · intro h i
    apply (seal_whole inter_subset_right _).mpr
    intro b hb v vb vs x xb
    exact mem_inter.mpr ⟨h b (mem_biUnion.mpr ⟨i,mem_univ _,hb⟩) v vb (mem_inter.mp vs).1 xb,where_block hb xb⟩
  · intro h b hb v vb vs x xb
    obtain ⟨i,_,bi⟩ := mem_biUnion.mp hb
    exact (mem_inter.mp ((seal_whole inter_subset_right _).mp (h i) b bi v vb
      (mem_inter.mpr ⟨vs,where_block bi vb⟩) xb)).1

/-- With a fixed partition into regions, the number of subdivisions also
respecting an extra cut is a product of two-cell counts, even at impossible sizes. -/
theorem decks_seal_card (z : V → I) (S : Finset V) :
    (decks z∩localSeal univ S).card=∏ i,sealWays (cell z i).card (S∩cell z i).card := by
  classical
  let M := Fintype.piFinset fun i => localSeal (cell z i) (S∩cell z i)
  have eq : decks z∩localSeal univ S=M.map (assemble z) := by
    ext D
    constructor
    · intro hd
      obtain ⟨P,_,rfl⟩ := mem_map.mp (mem_inter.mp hd).1
      exact mem_map.mpr ⟨P,Fintype.mem_piFinset.mpr ((assemble_seal _ _ _).mp (mem_inter.mp hd).2),rfl⟩
    · intro h
      obtain ⟨P,hm,rfl⟩ := mem_map.mp h
      exact mem_inter.mpr ⟨mem_map.mpr ⟨P,mem_univ _,rfl⟩,(assemble_seal _ _ _).mpr (Fintype.mem_piFinset.mp hm)⟩
  rw [eq,card_map,Fintype.card_piFinset]
  exact prod_congr rfl (fun _ _ => local_seal_ways _ _ inter_subset_right)

end Regions
end WildSieve
