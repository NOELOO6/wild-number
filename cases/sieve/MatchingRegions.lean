import TrimmedScopes
import RegionBudget
namespace WildSieve
open Finset
variable {A C : Type} [LinearOrder A] [Fintype A] [Fintype C]

omit [Fintype C] in
private theorem matching_regions (F : Factor A C) (c : C) (B R : Finset A) (outside : R⊆Bᶜ)
    (cl : Closed (F.f c) R) :
    ∃ (P : Finset A) (edge : A → Finset (Free B)), R.card=2*P.card ∧
      (∀ i∈P,(edge i).card=2) ∧ (P : Set A).PairwiseDisjoint edge ∧
      (points edge P).map (emb B)⊆R ∧
      ∀ S⊆P,Closed (F.f c) ((points edge S).map (emb B)) := by
  classical
  let p := F.f c
  let P := lowerEnds p R
  let edge (i : A) := toFree B {i,p i}
  have pairSub (i) (hi : i∈P) : {i,p i}⊆R := insert_subset (mem_filter.mp hi).1 (singleton_subset_iff.mpr (mem_filter.mp hi).2.2)
  have back (i) (hi : i∈P) : (edge i).map (emb B)={i,p i} := back_free ((pairSub i hi).trans outside)
  have memPair (i) (hi : i∈P) (x : Free B) (hx : x∈edge i) : x.val=i ∨ x.val=p i := by
    have old : (emb B) x ∈ (edge i).map (emb B) := mem_map.mpr ⟨x,hx,rfl⟩
    rwa [back i hi,mem_insert,mem_singleton] at old
  refine ⟨P,edge,closed_size (F.invol c) (F.moving c) cl,?_,?_,?_,?_⟩
  · intro i hi
    rw [←card_map (f:=emb B),back i hi]
    simp [F.moving c i,p]
  · intro i hi k hk ne
    apply disjoint_left.mpr
    intro v hv kv
    rcases memPair i hi v hv with a|a <;> rcases memPair k hk v kv with b|b
    · exact ne (a.symm.trans b)
    · have eq := a.symm.trans b
      have lt := (mem_filter.mp hi).2.1
      rw [eq,show p (p k)=k from F.invol c k] at lt
      exact lt.asymm (mem_filter.mp hk).2.1
    · have eq := b.symm.trans a
      have lt := (mem_filter.mp hk).2.1
      rw [eq,show p (p i)=i from F.invol c i] at lt
      exact lt.asymm (mem_filter.mp hi).2.1
    · exact ne ((F.invol c).injective (a.symm.trans b))
  · intro x hx
    obtain ⟨v,hv,rfl⟩ := mem_map.mp hx
    obtain ⟨i,hi,vi⟩ := mem_biUnion.mp hv
    have old : (emb B) v∈(edge i).map (emb B) := mem_map.mpr ⟨v,vi,rfl⟩
    exact pairSub i hi ((back i hi) ▸ old)
  · intro S sp v hv
    obtain ⟨w,hw,rfl⟩ := mem_map.mp hv
    obtain ⟨i,hi,wi⟩ := mem_biUnion.mp hw
    have member : p w.val∈(edge i).map (emb B) := by
      rw [back i (sp hi)]
      rcases memPair i (sp hi) w wi with eq|eq
      · exact mem_insert_of_mem (mem_singleton.mpr (congrArg p eq))
      · exact mem_insert.mpr (Or.inl ((congrArg p eq).trans (F.invol c i)))
    obtain ⟨z,hz,eq⟩ := mem_map.mp member
    exact mem_map.mpr ⟨z,mem_biUnion.mpr ⟨i,hi,hz⟩,eq⟩

private theorem excludes_cut {V : Type} [DecidableEq V] [Fintype V]
    {J : Finset Nat} {bad : Nat → Finset (Finset V)} {X Y : Finset V} {j : Nat}
    (level : j∈J) (cut : Y∈bad j) : localSeal X Y⊆(admissible J bad X)ᶜ := by
  classical
  intro M hm
  obtain ⟨L,lm⟩ := local_seal_mem.mp hm
  exact mem_compl.mpr fun ok => (mem_filter.mp ok).2 j level Y cut L lm

private theorem excludes_six (F : Factor A C) (c : C) (B : Finset A) (r : A) (f t : Nat)
    (X : Finset (Free B)) (P : Finset A) (edge : A → Finset (Free B))
    (sz : ∀ i∈P,(edge i).card=2) (apr : (P : Set A).PairwiseDisjoint edge)
    (cl : ∀ S⊆P,Closed (F.f c) ((points edge S).map (emb B))) :
    sixHits X P edge⊆(admissible shortLevels (badScopes F B r f t) X)ᶜ := by
  classical
  intro D hd
  obtain ⟨S,hs,hit⟩ := mem_biUnion.mp hd
  obtain ⟨sp,sc⟩ := mem_powersetCard.mp hs
  refine excludes_cut (j:=2) (by decide) ?_ hit
  exact (mem_gather _ _ _).mpr ⟨∅,short_empty _ _ _ _ _,pull_mem.mpr ⟨by rw [points_size P edge sz apr sp,sc],c,by simpa using cl S sp⟩⟩

theorem even_regions (F : Factor A C) (B : Finset A) (r : A) (f t j : Nat)
    (X : Finset (Free B)) (hit : X∈pullSides F B ∅ (3*j)) (lo : 4≤j) :
    (admissible shortLevels (badScopes F B r f t) X).card≤ways j-saving false (3*j/2) j := by
  classical
  obtain ⟨sz,c,cl⟩ := pull_mem.mp hit
  rw [empty_union] at cl
  obtain ⟨P,edge,pc,szE,apr,inX,closed⟩ := matching_regions F c B _ (map_free B X) cl
  rw [card_map,sz] at pc
  rw [show 3*j/2=P.card by omega]
  exact save_even X P edge szE apr (map_subset_map.mp inX) j sz lo _ (excludes_six F c B r f t X P edge szE apr closed)

theorem odd_regions (F : Factor A C) (B : Finset A) (r : A) (f t j : Nat) (hr : r∈B)
    (X : Finset (Free B)) (hit : X∈pullSides F B {r} (3*j)) (lo : 4≤j) :
    (admissible shortLevels (badScopes F B r f t) X).card≤ways j-saving true (3*j/2) j := by
  classical
  obtain ⟨sz,c,cl⟩ := pull_mem.mp hit
  let p := F.f c
  let S := X.map (emb B)
  let z := p r
  have rz : r≠z := F.moving c r
  have zS : z∈S := (mem_union.mp (cl r (mem_union_left _ (mem_singleton_self _)))).resolve_left (fun h => rz (mem_singleton.mp h).symm)
  have rS : r∉S := fun h => mem_compl.mp (map_free B X h) hr
  have pz : p z=r := F.invol c r
  let R := S.erase z
  have closed : Closed p R := by
    intro x hx
    obtain ⟨ne,xS⟩ := mem_erase.mp hx
    apply mem_erase.mpr
    refine ⟨fun eq => rS ((F.invol c).injective eq ▸ xS),?_⟩
    apply (mem_union.mp (cl x (mem_union_right _ xS))).resolve_left
    exact fun h => ne ((F.invol c).injective ((mem_singleton.mp h).trans pz.symm))
  have rs : R.card=3*j-1 := by rw [show R=S.erase z from rfl,card_erase_of_mem zS]; simp [S,sz]
  obtain ⟨P,edge,pc,szE,apr,inR,cls⟩ := matching_regions F c B R ((erase_subset _ _).trans (map_free B X)) closed
  let z' : Free B := ⟨z,map_free B X zS⟩
  have zX : z'∈X := by
    obtain ⟨v,hv,eq⟩ := mem_map.mp zS
    exact (show v=z' from Subtype.ext eq) ▸ hv
  have free : z'∉points edge P := fun h => (mem_erase.mp (inR (mem_map.mpr ⟨z',h,rfl⟩))).1 rfl
  have sub : points edge P⊆X := map_subset_map.mp (inR.trans (erase_subset _ _))
  rw [show 3*j/2=P.card by omega]
  apply save_odd X P edge z' szE apr sub zX free j sz lo _ (excludes_six F c B r f t X P edge szE apr cls)
  intro D hd
  obtain ⟨i,hi,occ⟩ := mem_biUnion.mp hd
  refine excludes_cut (j:=1) (by decide) ?_ occ
  have only : points edge {i}=edge i := by simp [points]
  have ci := cls {i} (singleton_subset_iff.mpr hi)
  rw [only] at ci
  have nz : z'∉edge i := fun h => free (mem_biUnion.mpr ⟨i,hi,h⟩)
  refine (mem_gather _ _ _).mpr ⟨{r},short_root _ _ _ _ _,pull_mem.mpr ⟨by simp [nz,szE i hi],c,?_⟩⟩
  rw [map_insert]
  intro v hv
  rcases mem_union.mp hv with x|x
  · rw [mem_singleton.mp x]
    exact mem_union_right _ (mem_insert_self _ _)
  rcases mem_insert.mp x with eq|x
  · change v=z at eq
    exact mem_union_left _ (mem_singleton.mpr (eq ▸ pz))
  · exact mem_union_right _ (mem_insert_of_mem (ci v x))
end WildSieve
