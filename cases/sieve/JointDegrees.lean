import DegreeChord
namespace WildSieve
open Finset
variable {A C : Type} [LinearOrder A] [Fintype A] [Fintype C]

def into (F : Factor A C) (x : A) (U : Finset A) := univ.filter fun c => F.f c x∈U

omit [Fintype A] in
theorem into_mem (F : Factor A C) (x : A) (U : Finset A) (c : C) :
    c∈into F x U ↔ F.f c x∈U := by simp [into]

omit [Fintype A] in
theorem into_size (F : Factor A C) (x : A) (U : Finset A) : (into F x U).card=(U.erase x).card := by
  classical
  rw [←card_image_of_injective _ (F.unique x)]
  congr 1
  ext y
  constructor
  · rintro h
    obtain ⟨c,hc,rfl⟩ := mem_image.mp h
    exact mem_erase.mpr ⟨(F.moving _ _).symm,(into_mem _ _ _ _).mp hc⟩
  · intro h
    obtain ⟨ne,hy⟩ := mem_erase.mp h
    obtain ⟨c,hc⟩ := F.edge x y ne.symm
    exact mem_image.mpr ⟨c,(into_mem _ _ _ _).mpr (hc ▸ hy),hc⟩

variable [DecidableEq C]

theorem into_compl (F : Factor A C) (x : A) (U : Finset A) : into F x Uᶜ=(into F x U)ᶜ := by
  ext c
  simp [into]

omit [Fintype A] [Fintype C] [DecidableEq C] in
private theorem one_inside (F : Factor A C) (c : C) (x : A) (G : Finset A) (hx : x∈G) (hy : F.f c x∈G) :
    1≤Inside F c G := by
  apply card_pos.mpr
  rcases lt_or_gt_of_ne (F.moving c x) with h|h
  · exact ⟨x,mem_filter.mpr ⟨hx,h,hy⟩⟩
  · exact ⟨_,mem_filter.mpr ⟨hy,by rwa [F.invol c x],by rwa [F.invol c x]⟩⟩

/-- The same outside pairs used to pay for extra three-point cuts are
unavailable to colors making six-point cuts through the marked point. -/
private theorem outside_credit (F : Factor A C) (U : Finset A) (r z : A) (hr : r∉U) (hz : z∈U)
    (c0 : C) (cz : F.f c0 r=z) :
    let K := into F r Uᶜ ∩ into F z Uᶜ
    let b := K.card+Inside F c0 Uᶜ
    (∑ c∈into F z U,Inside F c Uᶜ)≤Uᶜ.card.choose 2-b := by
  classical
  let K := into F r Uᶜ ∩ into F z Uᶜ
  let v (c : C) := Inside F c Uᶜ
  let S := into F z U
  have zeroOut : F.f c0 z=r := cz ▸ F.invol c0 r
  have noc : c0∉K := fun h => mem_compl.mp ((into_mem _ _ _ _).mp (mem_inter.mp h).1) (cz ▸ hz)
  have dis : Disjoint S (insert c0 K) := by
    apply disjoint_left.mpr
    intro c cs h
    have yes := (into_mem _ _ _ _).mp cs
    rcases mem_insert.mp h with rfl|k
    · exact hr (zeroOut ▸ yes)
    · exact mem_compl.mp ((into_mem _ _ _ _).mp (mem_inter.mp k).2) yes
  have paid : K.card≤∑ c∈K,v c := by
    calc
      K.card = ∑ _∈K,1 := by simp
      _ ≤ _ := sum_le_sum fun c hc => one_inside F c r _ (mem_compl.mpr hr) ((into_mem _ _ _ _).mp (mem_inter.mp hc).1)
  have total := sum_le_sum_of_subset_of_nonneg (f:=v) (subset_univ (S∪insert c0 K)) (fun _ _ _ => Nat.zero_le _)
  rw [sum_union dis,sum_insert noc] at total
  have all : (∑ c,v c)=Uᶜ.card.choose 2 := sum_inside F Uᶜ
  rw [all] at total
  change (∑ c∈S,v c)≤Uᶜ.card.choose 2-(K.card+v c0)
  omega

private theorem both_size (F : Factor A C) (U : Finset A) (r z : A) (hr : r∉U) (hz : z∈U)
    (large : Uᶜ.card<U.card) :
    (into F r U ∩ into F z U).card=U.card-Uᶜ.card+(into F r Uᶜ ∩ into F z Uᶜ).card := by
  classical
  let R := into F r U
  let Z := into F z U
  have rs : R.card=U.card := (into_size F r U).trans (congrArg card (erase_eq_of_not_mem hr))
  have zs : Zᶜ.card=Uᶜ.card := by
    rw [show Zᶜ=into F z Uᶜ from (into_compl F z U).symm,into_size,erase_eq_of_not_mem (by simpa using hz)]
  have parts (S T : Finset C) : (S∩T).card+(S∩Tᶜ).card=S.card := by
    rw [←card_union_of_disjoint (disjoint_left.mpr (fun c h k => mem_compl.mp (mem_inter.mp k).2 (mem_inter.mp h).2))]
    congr 1
    ext c
    simp only [mem_union,mem_inter,mem_compl]
    tauto
  have a := parts R Z
  have b := parts Zᶜ R
  rw [inter_comm Zᶜ R,inter_comm Zᶜ Rᶜ] at b
  rw [into_compl,into_compl]
  change (R∩Z).card=U.card-Uᶜ.card+(Rᶜ∩Zᶜ).card
  omega

omit [Fintype A] in
private theorem triple_degree (F : Factor A C) (U : Finset A) (r z : A) (hr : r∉U) (hz : z∈U)
    (c0 : C) (cz : F.f c0 r=z) :
    ((sides F {r} U 3).filter (fun X => z∈X)).card ≤ (into F r U ∩ into F z U).card+Inside F c0 U := by
  classical
  let fam (c : C) := (candidates F c {r} U 3).filter (fun X => z∈X)
  let S := into F r U ∩ into F z U
  let triple (c : C) : Finset A := {F.f c r,z,F.f c z}
  have strip (c : C) (X : Finset A) (hx : X∈fam c) :
      X⊆U ∧ X.card=3 ∧ F.f c r∈X ∧ Closed (F.f c) (X \ {F.f c r}) ∧ z∈X := by
    obtain ⟨hc,zx⟩ := mem_filter.mp hx
    obtain ⟨sub,sz,cl⟩ := candidate_mem.mp hc
    have dis : Disjoint X {r} := disjoint_singleton_right.mpr fun h => hr (sub h)
    have p := strip_fixed (F.invol c) (B:={r}) (D:={r}) Subset.rfl dis cl
    have force : forced (F.f c) {r} {r}={F.f c r} := by simp [forced,F.moving c r,(F.moving c r).symm]
    rw [force,singleton_subset_iff] at p
    exact ⟨sub,sz,p.1,p.2,zx⟩
  have cover : (sides F {r} U 3).filter (fun X => z∈X)⊆S.image triple ∪ fam c0 := by
    intro X hx
    obtain ⟨side,zx⟩ := mem_filter.mp hx
    obtain ⟨c,mem⟩ := side_mem.mp side
    have hit : X∈fam c := mem_filter.mpr ⟨mem,zx⟩
    by_cases eq : c=c0
    · exact mem_union_right _ (eq ▸ hit)
    obtain ⟨sub,sz,rc,cl,_⟩ := strip c X hit
    have ne : F.f c r≠z := fun e => eq (F.unique r (e.trans cz.symm))
    have other := cl z (mem_sdiff.mpr ⟨zx,by simpa using ne.symm⟩)
    have zc := (mem_sdiff.mp other).1
    have diff : F.f c r≠F.f c z := fun e => hr ((F.invol c).injective e ▸ hz)
    have ts : (triple c).card=3 := by simp [triple,ne,diff,F.moving c z]
    have sub3 : triple c⊆X := insert_subset rc (insert_subset zx (singleton_subset_iff.mpr zc))
    exact mem_union_left _ (mem_image.mpr ⟨c,mem_inter.mpr ⟨(into_mem _ _ _ _).mpr (sub rc),(into_mem _ _ _ _).mpr (sub zc)⟩,
      eq_of_subset_of_card_le sub3 (by omega)⟩)
  have count := count_free (F.invol c0) (F.moving c0) U {z} (fam c0) 3 (by
    intro X hx
    obtain ⟨sub,sz,_,cl,zx⟩ := strip c0 X hx
    exact ⟨sub,sz,singleton_subset_iff.mpr zx,cz ▸ cl⟩)
  rw [card_singleton] at count
  change (fam c0).card≤(lowerEnds (F.f c0) (U \ {z})).card.choose 1 at count
  rw [Nat.choose_one_right] at count
  have bound : (fam c0).card≤Inside F c0 U :=
    count.trans (card_le_card (lower_mono _ sdiff_subset))
  exact (card_le_card cover).trans ((card_union_le _ _).trans (Nat.add_le_add card_image_le bound))

/-- Joint upper bounds for both short cuts, with a shared outside-edge count. -/
theorem joint_degrees (F : Factor A C) (U : Finset A) (r z : A) (hr : r∉U) (hz : z∈U)
    (large : Uᶜ.card<U.card) (den : 0<Uᶜ.card/2) :
    ∃ b≤Uᶜ.card+Uᶜ.card/2,
      ((sides F {r} U 3).filter (fun X => z∈X)).card≤(U.card-Uᶜ.card)+(U.card-Uᶜ.card)/2+b ∧
      ((sides F ∅ U 6).filter (fun X => z∈X)).card≤chordPrice Uᶜ.card U.card b := by
  classical
  obtain ⟨c0,cz⟩ := F.edge r z (fun e => hr (e ▸ hz))
  let K := into F r Uᶜ ∩ into F z Uᶜ
  let i := Inside F c0 Uᶜ
  have ki : K.card≤Uᶜ.card := (card_le_card inter_subset_left).trans ((into_size F r Uᶜ).le.trans (card_le_card (erase_subset _ _)))
  have hi := ends_bound (F.invol c0) Uᶜ
  change 2*i≤Uᶜ.card at hi
  refine ⟨K.card+i,by omega,?_,six_local_price F U z hz large den _ (outside_credit F U r z hr hz c0 cz)⟩
  have part := free_pair_size (F.invol c0) (F.moving c0) Uᶜ
  rw [compl_compl] at part
  change 2*Inside F c0 U=U.card-(Uᶜ.card-2*i) at part
  have small := triple_degree F U r z hr hz c0 cz
  rw [both_size F U r z hr hz large] at small
  change _≤U.card-Uᶜ.card+K.card+Inside F c0 U at small
  omega
end WildSieve
