import GraphSieve
namespace WildExterior
open Finset WildSieve WildExact
abbrev Point := Fin 16
abbrev root : Point := Fin.last 15

private theorem small_side {D : Blocks Point} (tri : Triples D) (cover : vertices D=univ.erase root)
    (Q : Finset Point) (pos : Q.Nonempty) (whole : ∀ T∈D,Cohesive T Q)
    (small : Q.card≤8) (even : ∃ k,Q.card=2*k) :
    (∃ T∈D,Q=insert root T) ∨ (∃ T∈D,∃ U∈D,T≠U ∧ Q=T∪U) := by
  classical
  let M := D.filter (fun T => (T∩Q).Nonempty)
  have sub : M⊆D := filter_subset _ _
  have eq : vertices M=Q.erase root := by
    ext x
    constructor
    · intro h
      obtain ⟨T,ht,xt⟩ := mem_biUnion.mp h
      obtain ⟨td,y,yt⟩ := mem_filter.mp ht
      have all := block_sub td xt
      rw [cover] at all
      exact mem_erase.mpr ⟨(mem_erase.mp all).1,whole T td y (mem_inter.mp yt).1 x xt (mem_inter.mp yt).2⟩
    · intro h
      obtain ⟨nr,xq⟩ := mem_erase.mp h
      have xd : x∈vertices D := cover ▸ mem_erase.mpr ⟨nr,mem_univ _⟩
      obtain ⟨T,td,xt⟩ := mem_biUnion.mp xd
      exact mem_biUnion.mpr ⟨T,mem_filter.mpr ⟨td,x,mem_inter.mpr ⟨xt,xq⟩⟩,xt⟩
  have n := (tri.sub sub).card_vertices
  rw [eq] at n
  have p := card_pos.mpr pos
  obtain ⟨k,hk⟩ := even
  by_cases rq : root∈Q
  · rw [card_erase_of_mem rq] at n
    obtain ⟨T,mt⟩ := card_eq_one.mp (show M.card=1 by omega)
    have td : T∈D := sub (mt ▸ mem_singleton_self _)
    have e : T=Q.erase root := by simpa only [mt,vertices_singleton] using eq
    exact Or.inl ⟨T,td,by rw [e,insert_erase rq]⟩
  · rw [erase_eq_of_not_mem rq] at n eq
    obtain ⟨T,U,ne,ms⟩ := card_eq_two.mp (show M.card=2 by omega)
    have td : T∈D := sub (ms ▸ mem_insert_self _ _)
    have ud : U∈D := sub (ms ▸ mem_insert_of_mem (mem_singleton_self _))
    exact Or.inr ⟨T,td,U,ud,ne,by simpa [ms,vertices] using eq.symm⟩

theorem small_closed_side (g : Coloring 15 15) (w : Lines 15) (c x y : Fin 15)
    (lost : ¬WildDeletion.Walk (Joined g w c) x y)
    (D : Blocks Point) (tri : Triples D) (cover : vertices D=univ.erase root)
    (joined : ∀ Q : Finset Point,
      (∀ T : Finset Point,root∉T → spokes (oldPart T)⊆w → Cohesive T Q) → ∀ T∈D,Cohesive T Q) :
    ∃ Q : Finset Point, Closed ((coloringFactor (augment (by decide) g)).f c) Q ∧
      (∀ T : Finset Point,root∉T → spokes (oldPart T)⊆w → Cohesive T Q) ∧
      ((∃ T∈D,Q=insert root T) ∨ (∃ T∈D,∃ U∈D,T≠U ∧ Q=T∪U)) := by
  let F := coloringFactor (augment (by decide) g)
  obtain ⟨S,l,r,cl,wh⟩ := closed_side_of_failure g (by decide) w c x y lost
  have choose (Q : Finset Point) (pos : Q.Nonempty) (cq : Closed (F.f c) Q)
      (small : Q.card≤8) (all : ∀ T : Finset Point,root∉T → spokes (oldPart T)⊆w → Cohesive T Q) :
      (∃ T∈D,Q=insert root T) ∨ (∃ T∈D,∃ U∈D,T≠U ∧ Q=T∪U) := by
    apply small_side tri cover Q pos _ small ⟨_,closed_size (F.invol c) (F.moving c) cq⟩
    exact joined Q all
  by_cases size : S.card≤8
  · exact ⟨S,cl,wh,choose S l cl size wh⟩
  · have cc : Closed (F.f c) Sᶜ := fun v hv => mem_compl.mpr (fun fs => mem_compl.mp hv (F.invol c v ▸ cl _ fs))
    have hc (T : Finset Point) (nr : root∉T) (edges : spokes (oldPart T)⊆w) : Cohesive T Sᶜ := by
      intro a ha b hb na
      exact mem_compl.mpr (fun bs => mem_compl.mp na (wh T nr edges b hb a ha bs))
    obtain ⟨v,nv⟩ := r
    have r : Sᶜ.Nonempty := ⟨v,mem_compl.mpr nv⟩
    refine ⟨Sᶜ,cc,hc,choose Sᶜ r cc ?_ hc⟩
    rw [card_compl,Fintype.card_fin];omega

def drawing (D : Blocks Point) := D.biUnion (fun T => spokes (oldPart T))

theorem draw_mem {D : Blocks Point} {T : Finset Point} (ht : T∈D) :
    spokes (oldPart T)⊆drawing D := fun _ h => mem_biUnion.mpr ⟨T,ht,h⟩

theorem draw_legal (D : Blocks Point) : Legal (drawing D) := by
  intro e he
  obtain ⟨T,_,h⟩ := mem_biUnion.mp he
  exact spokes_legal _ e h

theorem drawing_size (D : Blocks Point) (tri : Triples D) (cover : vertices D=univ.erase root) :
    (drawing D).card≤10 := by
  have sz := tri.card_vertices
  rw [cover,card_erase_of_mem (mem_univ _),card_univ,Fintype.card_fin] at sz
  have five : D.card=5 := by omega
  apply card_biUnion_le.trans
  calc
    _≤∑ _∈D,2 := sum_le_sum (fun T ht => (spokes_bound _).trans (by
      have nr : root∉T := fun h => not_mem_erase _ _ (cover ▸ block_sub ht h)
      rw [old_size T nr,tri.size T ht]))
    _=10 := by simp [five]

/-- A partition into five triples is enough as soon as every root-plus-triple
and every union of two triples is crossed by every color. -/
theorem ten_from_five (g : Coloring 15 15) (D : Blocks Point) (tri : Triples D)
    (cover : vertices D=univ.erase root)
    (one : ∀ c T,T∈D → ¬Closed ((coloringFactor (augment (by decide) g)).f c) (insert root T))
    (two : ∀ c T,T∈D → ∀ U,U∈D → T≠U → ¬Closed ((coloringFactor (augment (by decide) g)).f c) (T∪U)) :
    Upper g 10 := by
  refine ⟨drawing D,draw_legal D,drawing_size D tri cover,?_⟩
  intro c x y
  by_contra lost
  have joined Q (all : ∀ T : Finset Point,root∉T → spokes (oldPart T)⊆drawing D → Cohesive T Q)
      (T) (ht : T∈D) := all T (fun h => not_mem_erase _ _ (cover ▸ block_sub ht h)) (draw_mem ht)
  obtain ⟨Q,cl,_,side⟩ := small_closed_side g _ c x y lost D tri cover joined
  rcases side with ⟨T,ht,rfl⟩|⟨T,ht,U,hu,ne,rfl⟩
  · exact one c _ ht cl
  · exact two c _ ht _ hu ne cl
end WildExterior
