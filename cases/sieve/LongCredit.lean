import MatchingSixes
import LayoutSplit
import RegionBudget
namespace WildSieve
open Finset
variable {A C : Type} [LinearOrder A] [Fintype A] [Fintype C]

/-- Subdivisions of X avoiding every marked six contained in X. -/
noncomputable def noSix (F : Factor A C) (X : Finset A) :=
  (univ : Finset (Layout X)).filter (fun D => ∀ Q∈marks F X,D∉localSeal X Q)

theorem noSix_mem {F : Factor A C} {X : Finset A} {D : Layout X} :
    D∈noSix F X ↔ ∀ Q∈marks F X,D∉localSeal X Q := by classical simp [noSix]

/-- A color closing X provides three-edge submatchings. On surviving
layouts, none of their six-point supports can be sealed. -/
theorem inside_noSix (F : Factor A C) (X : Finset A) (c : C) (cl : Closed (F.f c) X)
    (j : Nat) (size : X.card=3*j) (lo : 4≤j) :
    (noSix F X).card≤ways j-saving false (3*j/2) j := by
  classical
  let f := F.f c
  let P := lowerEnds f X
  let edge (i : A) : Finset A := {i,f i}
  have pts (I : Finset A) : points edge I=I∪I.image f := by
    ext v
    simp only [points,mem_biUnion,edge,mem_insert,mem_singleton,mem_union,mem_image]
    constructor
    · rintro ⟨a,ai,e|e⟩
      · exact Or.inl (e.symm ▸ ai)
      · exact Or.inr ⟨a,ai,e.symm⟩
    · rintro (h|⟨a,ai,e⟩)
      · exact ⟨v,h,Or.inl rfl⟩
      · exact ⟨a,ai,Or.inr e.symm⟩
  have valid (i) (_ : i∈P) : (edge i).card=2 := by simp [edge,f,F.moving c i]
  have apart : (P : Set A).PairwiseDisjoint edge := by
    intro i hi k hk ne
    apply disjoint_left.mpr
    intro v hv kv
    change v∈{i,f i} at hv
    change v∈{k,f k} at kv
    simp only [mem_insert,mem_singleton] at hv kv
    rcases hv with a|a <;> rcases kv with b|b
    · exact ne (a.symm.trans b)
    · have eq := a.symm.trans b
      have lt := (mem_filter.mp hi).2.1
      change i<f i at lt
      rw [eq,show f (f k)=k from F.invol c k] at lt
      exact lt.asymm (mem_filter.mp hk).2.1
    · have eq := b.symm.trans a
      have lt := (mem_filter.mp hk).2.1
      change k<f k at lt
      rw [eq,show f (f i)=i from F.invol c i] at lt
      exact lt.asymm (mem_filter.mp hi).2.1
    · exact ne ((F.invol c).injective (a.symm.trans b))
  have psize := closed_size (F.invol c) (F.moving c) cl
  change X.card=2*P.card at psize
  have full : points edge P⊆X := by rw [pts,recover_ends (F.invol c) (F.moving c) cl]
  have lose : sixHits X P edge⊆(noSix F X)ᶜ := by
    intro D h
    obtain ⟨I,hi,cut⟩ := mem_biUnion.mp h
    obtain ⟨sub,three⟩ := mem_powersetCard.mp hi
    obtain ⟨ix,sz,icl,_⟩ := close_lowers F c sub
    have m : points edge I∈marks F X := by rw [pts];exact mark_mem.mpr ⟨ix,sz.trans (congrArg (2*·) three),c,icl⟩
    exact mem_compl.mpr (fun ok => noSix_mem.mp ok _ m cut)
  rw [show 3*j/2=P.card by omega]
  exact save_even X P edge valid apart full j size lo _ lose

/-- A sealed cut splits a surviving layout into two subdivisions, each of
which avoids the marked six-sets on its own side. -/
theorem noSix_product (F : Factor A C) (S : Finset A) :
    (noSix F univ∩localSeal univ S).card≤(noSix F S).card*(noSix F Sᶜ).card := by
  classical
  let U := (univ:Finset A) \ S
  have eq : U=Sᶜ := by ext; simp [U]
  have bound := split_upper univ S (subset_univ _) _ (noSix F S) (noSix F U)
    (inter_subset_right : noSix F univ∩localSeal univ S⊆localSeal univ S) (fun P h => by
      have pass := noSix_mem.mp (mem_inter.mp h).1
      constructor
      · apply noSix_mem.mpr
        intro Q hq cut
        obtain ⟨sub,qs,qcl⟩ := mark_mem.mp hq
        exact pass Q (mark_mem.mpr ⟨subset_univ _,qs,qcl⟩) ((seal_glue_left univ S Q _ P sub).mpr cut)
      · apply noSix_mem.mpr
        intro Q hq cut
        obtain ⟨sub,qs,qcl⟩ := mark_mem.mp hq
        exact pass Q (mark_mem.mpr ⟨subset_univ _,qs,qcl⟩) ((seal_glue_right univ S Q _ P sub).mpr cut))
  simpa only [eq] using bound

/-- When a large set is closed by a matching, both its sides must avoid
their smaller marks. Their subdivisions can be counted independently. -/
theorem long_noSix (F : Factor A C) (S : Finset A) (c : C) (cl : Closed (F.f c) S)
    (i j : Nat) (sz : S.card=3*i) (other : Sᶜ.card=3*j) (il : 4≤i) (jl : 4≤j) :
    ((noSix F univ)∩localSeal univ S).card≤
      (ways i-saving false (3*i/2) i)*(ways j-saving false (3*j/2) j) := by
  have closedU : Closed (F.f c) Sᶜ := by
    intro x hx
    exact mem_compl.mpr fun h => mem_compl.mp hx (F.invol c x ▸ cl _ h)
  exact (noSix_product F S).trans (Nat.mul_le_mul (inside_noSix F S c cl i sz il)
    (inside_noSix F Sᶜ c closedU j other jl))
end WildSieve
