import MatchingSixes
namespace WildSieve
open Finset
variable {A C : Type} [LinearOrder A]
theorem mixed_six_color (F : Factor A C) (c : C) (S W : Finset A)
    (six : S.card=6) (H : Finset (Finset A))
    (valid : ∀ Q∈H,Q⊆S∪W ∧ Q.card=6 ∧ (Q∩S).card=3 ∧ Closed (F.f c) Q) :
    H.card≤(6-2*Inside F c S).choose 3 + Inside F c S*(6-2*Inside F c S)*Inside F c W := by
  classical
  let f := F.f c
  let E := S \ paired f S
  let B := lowerEnds f S
  let O := lowerEnds f W
  let edge (x : A) : Finset A := {x,f x}
  let pure := (E.powersetCard 3).image (fun D => D∪D.image f)
  let mix := ((B×ˢE)×ˢO).image (fun p => edge p.1.1∪edge p.1.2∪edge p.2)
  have edge_in (Q : Finset A) (cl : Closed f Q) (x) (xq : x∈Q) : edge x⊆Q :=
    insert_subset xq (singleton_subset_iff.mpr (cl x xq))
  have memE (x) (xs : x∈S) (fs : f x∉S) : x∈E := mem_sdiff.mpr ⟨xs,fun h => fs (mem_filter.mp h).2⟩
  have cover : H⊆pure∪mix := by
    intro Q hq
    obtain ⟨sub,qs,three,cl⟩ := valid Q hq
    let D := Q∩S
    have dq : D⊆Q := inter_subset_left
    have ds : D⊆S := inter_subset_right
    have sz : D.card=3 := three
    by_cases closedPair : ∃ y∈D,f y∈D
    · obtain ⟨y,yd,fy⟩ := closedPair
      let z := min y (f y)
      have parts : (z=y ∧ f z=f y) ∨ (z=f y ∧ f z=y) := by
        rcases le_total y (f y) with h|h
        · exact Or.inl ⟨min_eq_left h,congrArg f (min_eq_left h)⟩
        · exact Or.inr ⟨min_eq_right h,(congrArg f (min_eq_right h)).trans (F.invol c y)⟩
      have zlt : z<f z := by
        rcases lt_or_gt_of_ne (F.moving c y) with h|h
        · rw [show z=y from min_eq_left h.le]; exact h
        · rw [show z=f y from min_eq_right h.le,show f (f y)=y from F.invol c y]; exact h
      have zd : z∈D ∧ f z∈D := by rcases parts with ⟨h,k⟩|⟨h,k⟩ <;> rw [k,h] <;> tauto
      have ed : edge z⊆D := insert_subset zd.1 (singleton_subset_iff.mpr zd.2)
      have esize (v : A) : (edge v).card=2 := by simp [edge,f,F.moving c v]
      have one : (D \ edge z).card=1 := by rw [card_sdiff ed,sz,esize]
      obtain ⟨x,xeq⟩ := card_eq_one.mp one
      have xd : x∈D \ edge z := xeq ▸ mem_singleton_self x
      have drep : edge z∪{x}=D := xeq ▸ union_sdiff_of_subset ed
      have px : f x∉S := by
        intro fx
        have fd : f x∈D := mem_inter.mpr ⟨cl x (dq (mem_sdiff.mp xd).1),fx⟩
        rw [←drep] at fd
        rcases mem_union.mp fd with h|h
        · rcases (mem_insert.mp h) with h|h
          · have e : x=f z := (F.invol c x).symm.trans (congrArg f h)
            exact (mem_sdiff.mp xd).2 (mem_insert_of_mem (mem_singleton.mpr e))
          · have e := (F.invol c).injective (mem_singleton.mp h)
            exact (mem_sdiff.mp xd).2 (mem_insert.mpr (Or.inl e))
        · exact (F.moving c x).symm (mem_singleton.mp h)
      let V := edge z∪edge x
      have dis : Disjoint (edge z) (edge x) := by
        apply disjoint_left.mpr
        intro v vz vx
        rcases mem_insert.mp vx with e|e
        · exact (mem_sdiff.mp xd).2 (e ▸ vz)
        · exact px ((mem_singleton.mp e) ▸ ds (ed vz))
      have vsize : V.card=4 := by rw [show V=edge z∪edge x from rfl,card_union_of_disjoint dis,esize,esize]
      have incl := union_subset (edge_in Q cl z (dq zd.1)) (edge_in Q cl x (dq (mem_sdiff.mp xd).1))
      change V⊆Q at incl
      have two : (Q \ V).card=2 := by rw [card_sdiff incl,qs,vsize]
      have insideW : Q \ V⊆W := by
        intro p hp
        apply (mem_union.mp (sub (mem_sdiff.mp hp).1)).resolve_left
        intro ps
        have pd : p∈D := mem_inter.mpr ⟨(mem_sdiff.mp hp).1,ps⟩
        rw [←drep] at pd
        exact (mem_sdiff.mp hp).2 ((union_subset subset_union_left (singleton_subset_iff.mpr (mem_union_right _ (mem_insert_self _ _)))) pd)
      have ecl (t : A) : Closed f (edge t) := by
        intro v hv
        rcases mem_insert.mp hv with e|e
        · exact mem_insert_of_mem (mem_singleton.mpr (congrArg f e))
        · exact mem_insert.mpr (Or.inl ((congrArg f (mem_singleton.mp e)).trans (F.invol c t)))
      have rest : Closed f (Q \ V) := by
        intro v h
        refine mem_sdiff.mpr ⟨cl v (mem_sdiff.mp h).1,fun bad => (mem_sdiff.mp h).2 ?_⟩
        rcases mem_union.mp bad with k|k
        · exact mem_union_left _ (F.invol c v ▸ ecl z _ k)
        · exact mem_union_right _ (F.invol c v ▸ ecl x _ k)
      have rc := closed_size (F.invol c) (F.moving c) rest
      change (Q \ V).card=2*(lowerEnds f (Q \ V)).card at rc
      have cnt : (lowerEnds f (Q \ V)).card=1 := by omega
      obtain ⟨u,ue⟩ := card_eq_one.mp cnt
      have ul : u∈lowerEnds f (Q \ V) := ue ▸ mem_singleton_self u
      have last := recover_ends (F.invol c) (F.moving c) rest
      rw [ue] at last
      have ueq : edge u=Q \ V := by simpa [edge] using last
      exact mem_union_right _ (mem_image.mpr ⟨((z,x),u),mem_product.mpr ⟨mem_product.mpr
        ⟨mem_filter.mpr ⟨ds zd.1,zlt,ds zd.2⟩,memE x (ds (mem_sdiff.mp xd).1) px⟩,lower_mono f insideW ul⟩,
        (congrArg (V∪·) ueq).trans (union_sdiff_of_subset incl)⟩)
    · have extd (x) (h : x∈D) : f x∉S := fun fs => closedPair ⟨x,h,mem_inter.mpr ⟨cl x (dq h),fs⟩⟩
      have de : D⊆E := fun x hx => memE x (ds hx) (extd x hx)
      have dis : Disjoint D (D.image f) := by
        apply disjoint_left.mpr
        intro x dx h
        obtain ⟨y,yd,rfl⟩ := mem_image.mp h
        exact extd y yd (ds dx)
      have size : (D∪D.image f).card=6 := by rw [card_union_of_disjoint dis,card_image_of_injective _ (F.invol c).injective,sz]
      have subQ : D∪D.image f⊆Q := union_subset dq (by
        rintro v h
        obtain ⟨y,yd,rfl⟩ := mem_image.mp h
        exact cl y (dq yd))
      exact mem_union_left _ (mem_image.mpr ⟨D,mem_powersetCard.mpr ⟨de,sz⟩,eq_of_subset_of_card_le subQ (by omega)⟩)
  have ec : E.card=6-2*Inside F c S := by
    rw [show E=S \ paired f S from rfl,card_sdiff (show paired f S⊆S from filter_subset _ _),paired_size (F.invol c) (F.moving c),six];rfl
  have one : pure.card≤(E.powersetCard 3).card := card_image_le
  have two : mix.card≤((B×ˢE)×ˢO).card := card_image_le
  exact (card_le_card cover).trans ((card_union_le pure mix).trans (by
    simpa only [card_powersetCard,card_product,ec,Inside,B,O] using Nat.add_le_add one two))
end WildSieve
