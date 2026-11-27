import FrozenLayout
namespace WildSieve
open Finset
variable {A C : Type} [LinearOrder A] [Fintype A] [Fintype C]

def Cohesive (T S : Finset A) := ∀ x∈T, ∀ y∈T, x∈S → y∈S

theorem Cohesive.complement {T S : Finset A} (h : Cohesive T S) : Cohesive T Sᶜ :=
  fun x hx y hy nx => mem_compl.mpr (fun ys => mem_compl.mp nx (h y hy x hx ys))

def selected {B : Finset A} (L : Layout (univ : Finset (Free B))) (S : Finset A) :=
  L.val.filter fun T => ((T.map (emb B)) ∩ S).Nonempty

private theorem selected_mem {B : Finset A} (L : Layout (univ : Finset (Free B))) (S : Finset A)
    (whole : ∀ T∈L.val,Cohesive (T.map (emb B)) S) (x : Free B) :
    x ∈ vertices (selected L S) ↔ x.val∈S := by
  classical
  constructor
  · intro hx
    obtain ⟨T,ht,xt⟩ := mem_biUnion.mp hx
    obtain ⟨tl,y,hy⟩ := mem_filter.mp ht
    obtain ⟨ym,ys⟩ := mem_inter.mp hy
    exact whole T tl y ym x.val (mem_map.mpr ⟨x,xt,rfl⟩) ys
  · intro hx
    obtain ⟨T,tl,xt⟩ := mem_biUnion.mp (show x∈vertices L.val by rw [L.property.2]; simp)
    exact mem_biUnion.mpr ⟨T,mem_filter.mpr ⟨tl,x.val,mem_inter.mpr ⟨mem_map.mpr ⟨x,xt,rfl⟩,hx⟩⟩,xt⟩

private theorem side_eq {B : Finset A} (L : Layout (univ : Finset (Free B))) (S : Finset A)
    (whole : ∀ T∈L.val,Cohesive (T.map (emb B)) S) :
    S∩B ∪ (vertices (selected L S)).map (emb B)=S := by
  ext x
  constructor
  · intro h
    rcases mem_union.mp h with hi|im
    · exact (mem_inter.mp hi).1
    · obtain ⟨v,hv,rfl⟩ := mem_map.mp im
      exact (selected_mem L S whole v).mp hv
  · intro xs
    by_cases xb : x∈B
    · exact mem_union_left _ (mem_inter.mpr ⟨xs,xb⟩)
    · let v : Free B := ⟨x,mem_compl.mpr xb⟩
      exact mem_union_right _ (mem_map.mpr ⟨v,(selected_mem L S whole v).mpr xs,rfl⟩)

private theorem count_complement {B : Finset A} (L : Layout (univ : Finset (Free B))) (S : Finset A)
    (whole : ∀ T∈L.val,Cohesive (T.map (emb B)) S) :
    (selected L S).card+(selected L Sᶜ).card = L.val.card := by
  have eq : selected L Sᶜ = L.val \ selected L S := by
    ext T
    constructor
    · intro h
      obtain ⟨inL,x,hx⟩ := mem_filter.mp h
      refine mem_sdiff.mpr ⟨inL,?_⟩
      rintro sel
      obtain ⟨_,y,hy⟩ := mem_filter.mp sel
      exact mem_compl.mp (mem_inter.mp hx).2 (whole _ inL _ (mem_inter.mp hy).1 _ (mem_inter.mp hx).1 (mem_inter.mp hy).2)
    · intro h
      obtain ⟨inL,ns⟩ := mem_sdiff.mp h
      obtain ⟨x,hx⟩ := card_pos.mp (show 0<T.card by rw [L.property.1.size _ inL]; decide)
      have xm : x.val∈T.map (emb B) := mem_map.mpr ⟨x,hx,rfl⟩
      refine mem_filter.mpr ⟨inL,x.val,mem_inter.mpr ⟨xm,mem_compl.mpr ?_⟩⟩
      exact fun xs => ns (mem_filter.mpr ⟨inL,x.val,mem_inter.mpr ⟨xm,xs⟩⟩)
  rw [eq,Nat.add_comm]
  exact card_sdiff_add_card_eq_card (filter_subset _ _)

omit [Fintype A] in
private theorem side_choice (B S : Finset A) (root : A) (rb : root∈B) (f t j : Nat)
    (bs : B.card=f+1) (fixed : Cohesive (B.erase root) S)
    (small : 2*j<t ∨ Disjoint (B.erase root) S) : S∩B∈choices B root f t j := by
  classical
  by_cases dis : Disjoint (B.erase root) S
  · have base : S∩B=if root∈S then {root} else ∅ := by
      ext x
      by_cases eq : x=root
      · subst x
        by_cases r : root∈S <;> simp [r,rb]
      · have no : x∈S → x∉B := fun xs xb => disjoint_left.mp dis (mem_erase.mpr ⟨eq,xb⟩) xs
        by_cases r : root∈S <;> simp [r,eq] <;> exact no
    rw [base]
    by_cases r : root∈S <;> simp [choices,r]
  · obtain ⟨x,xf,xs⟩ := not_disjoint_iff.mp dis
    have all : B.erase root⊆S := fun y hy => fixed x xf y hy xs
    have positive : 0<f := by
      have cnt := card_pos.mpr (show (B.erase root).Nonempty from ⟨x,xf⟩)
      rw [card_erase_of_mem rb,bs] at cnt
      omega
    have elig : 0<f ∧ 2*j<t := ⟨positive,small.resolve_right dis⟩
    by_cases r : root∈S
    · have sub : B⊆S := by
        intro y hy
        by_cases yr : y=root
        · exact yr ▸ r
        · exact all (mem_erase.mpr ⟨yr,hy⟩)
      simp [choices,elig,inter_eq_right.mpr sub]
    · have eq : S∩B=B.erase root := by
        ext y
        exact ⟨fun h => mem_erase.mpr ⟨fun yr => r (yr ▸ (mem_inter.mp h).1),(mem_inter.mp h).2⟩,
          fun h => mem_inter.mpr ⟨all h,(mem_erase.mp h).2⟩⟩
      simp [choices,elig,eq]

omit [Fintype A] [Fintype C] in
private theorem unfrozen_point (F : Factor A C) (B S : Finset A) (c : C) (root : A) (f : Nat)
    (rain : Rainbow F B) (rb : root∈B) (bs : B.card=f+1) (shape : f=0 ∨ 3≤f)
    (ne : S.Nonempty) (cl : Closed (F.f c) S) (fixed : Cohesive (B.erase root) S) :
    ¬ S⊆B := by
  intro sub
  have cap := (inside_mono F c sub).trans (rain c)
  have even := closed_size (F.invol c) (F.moving c) cl
  change (lowerEnds (F.f c) S).card ≤ 1 at cap
  have two : S.card=2 := by have := card_pos.mpr ne; omega
  have somebody : ¬ S ⊆ {root} := by
    intro singleton
    have bound := card_le_card singleton
    simp [two] at bound
  obtain ⟨x,xs,xr⟩ := Finset.not_subset.mp somebody
  have xf : x∈B.erase root := mem_erase.mpr ⟨fun eq => xr (eq ▸ mem_singleton_self _),sub xs⟩
  have all : B.erase root ⊆ S := fun y hy => fixed x xf y hy xs
  have le := card_le_card all
  have pos := card_pos.mpr (show (B.erase root).Nonempty from ⟨x,xf⟩)
  rw [card_erase_of_mem rb,bs] at le pos
  omega

/-- A layout avoiding the counted seals has no nontrivial matching-closed
union of whole blocks, with the root allowed on either side. -/
theorem no_cut (F : Factor A C) (B : Finset A) (root : A) (f t : Nat)
    (rb : root∈B) (bs : B.card=f+1) (ws : Bᶜ.card=3*t) (rain : Rainbow F B)
    (shape : f=0 ∨ 3≤f) (L : Layout (univ : Finset (Free B)))
    (wins : ∀ j∈shortLevels ∪ longLevels t, ∀ X∈badScopes F B root f t j,L∉sealEvent X)
    (c : C) (S : Finset A) (left : S.Nonempty) (right : Sᶜ.Nonempty)
    (cl : Closed (F.f c) S) (fixed : Cohesive (B.erase root) S)
    (whole : ∀ T∈L.val,Cohesive (T.map (emb B)) S) : False := by
  classical
  have against (Y : Finset A) (ny : Y.Nonempty) (cy : Closed (F.f c) Y) (fy : Cohesive (B.erase root) Y)
      (wy : ∀ T∈L.val,Cohesive (T.map (emb B)) Y) (half : 2*(selected L Y).card≤t)
      (pick : 2*(selected L Y).card<t ∨ Disjoint (B.erase root) Y) : False := by
    let P := selected L Y
    let X := vertices P
    let j := P.card
    have part : Triples P := L.property.1.sub (filter_subset _ _)
    have nx : 0<j := by
      by_contra! zero
      have empty : P=∅ := card_eq_zero.mp (by omega)
      have eq := side_eq L Y wy
      change Y∩B ∪ (vertices P).map (emb B)=Y at eq
      simp [empty,vertices] at eq
      exact unfrozen_point F B Y c root f rain rb bs shape ny cy fy eq
    have level : j∈shortLevels ∪ longLevels t := by
      change 2*j≤t at half
      by_cases two : j≤2
      · apply mem_union_left
        simp only [shortLevels,mem_insert,mem_singleton]
        omega
      · exact mem_union_right _ (mem_filter.mpr ⟨mem_range.mpr (by omega),by omega⟩)
    have inBad : X∈badScopes F B root f t j :=
      (mem_gather _ _ _).mpr ⟨Y∩B,side_choice B Y root rb f t j bs fy pick,
        pull_mem.mpr ⟨part.card_vertices,c,by rwa [show Y∩B ∪ X.map (emb B)=Y from side_eq L Y wy]⟩⟩
    exact wins j level X inBad (mem_seal.mpr ⟨⟨P,part,rfl⟩,filter_subset _ _⟩)
  have wc (T) (ht : T∈L.val) := (whole T ht).complement
  have cc : Closed (F.f c) Sᶜ := fun x hx => mem_compl.mpr (fun fs => mem_compl.mp hx
    (by simpa [F.invol c x] using cl (F.f c x) fs))
  have cnt := count_complement L S whole
  have n := L.property.1.card_vertices
  rw [L.property.2,card_univ,Fintype.card_coe,ws] at n
  by_cases a : 2*(selected L S).card<t
  · exact against S left cl fixed whole a.le (Or.inl a)
  by_cases b : 2*(selected L Sᶜ).card<t
  · exact against Sᶜ right cc fixed.complement wc b.le (Or.inl b)
  by_cases dis : Disjoint (B.erase root) S
  · exact against S left cl fixed whole (by omega) (Or.inr dis)
  obtain ⟨x,hx,xs⟩ := not_disjoint_iff.mp dis
  have dc : Disjoint (B.erase root) Sᶜ := disjoint_left.mpr (fun y hy yc => mem_compl.mp yc (fixed x hx y hy xs))
  exact against Sᶜ right cc fixed.complement wc (by omega) (Or.inr dc)

end WildSieve
