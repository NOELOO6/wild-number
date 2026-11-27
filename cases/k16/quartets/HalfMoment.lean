import FrozenStats
namespace WildSieve
open Finset
variable {A C : Type} [LinearOrder A] [Fintype A] [Fintype C]

omit [Fintype C] in
/-- Sum the number of k whole edges in every s-point set, for one fixed
matching. A given choice of k edges uses exactly 2k prescribed points. -/
theorem matching_moment (F : Factor A C) (c : C) (s k : Nat) :
    (∑ S∈(univ : Finset A).powersetCard s,(Inside F c S).choose k) ≤
      ((Fintype.card A)/2).choose k * ((Fintype.card A)-2*k).choose (s-2*k) := by
  classical
  let f := F.f c
  let L := lowerEnds f univ
  let P := L.powersetCard k
  let cuts := (univ : Finset A).powersetCard s
  let U (E : Finset A) := E ∪ E.image f
  have complete : Closed f univ := fun _ _ => mem_univ _
  have total := closed_size (F.invol c) (F.moving c) complete
  rw [card_univ] at total
  change Fintype.card A=2*L.card at total
  have supp (E) (he : E∈P) : (U E).card=2*k := by
    obtain ⟨sub,sz⟩ := mem_powersetCard.mp he
    have dis : Disjoint E (E.image f) := by
      apply disjoint_left.mpr
      intro x xe xim
      obtain ⟨y,ye,rfl⟩ := mem_image.mp xim
      have a := (mem_filter.mp (sub xe)).2.1
      have b := (mem_filter.mp (sub ye)).2.1
      change f y<f (f y) at a
      have inv : f (f y)=y := F.invol c y
      rw [inv] at a
      exact a.asymm b
    dsimp [U]
    rw [card_union_of_disjoint dis,card_image_of_injective _ (F.invol c).injective,sz]
    omega
  have count (S : Finset A) : (Inside F c S).choose k =
      ∑ E∈P, if U E⊆S then 1 else 0 := by
    rw [sum_boole]
    change (lowerEnds f S).card.choose k=_
    rw [← card_powersetCard]
    congr 1
    ext E
    simp only [P,mem_filter,mem_powersetCard]
    constructor
    · rintro ⟨sub,sz⟩
      refine ⟨⟨sub.trans (lower_mono f (subset_univ _)),sz⟩,?_⟩
      intro x hx
      rcases mem_union.mp hx with e|e
      · exact (mem_filter.mp (sub e)).1
      obtain ⟨v,ve,rfl⟩ := mem_image.mp e
      exact (mem_filter.mp (sub ve)).2.2
    · rintro ⟨⟨sub,sz⟩,ok⟩
      refine ⟨fun x hx => mem_filter.mpr ⟨ok (mem_union_left _ hx),(mem_filter.mp (sub hx)).2.1,?_⟩,sz⟩
      exact ok (mem_union_right _ (mem_image.mpr ⟨x,hx,rfl⟩))
  have extension (E) (he : E∈P) :
      (∑ S∈cuts, if U E⊆S then 1 else 0) ≤ ((Fintype.card A)-2*k).choose (s-2*k) := by
    rw [sum_boole]
    have szU : (U E)ᶜ.card=Fintype.card A-2*k := by rw [card_compl,supp E he]
    rw [show ((Fintype.card A)-2*k).choose (s-2*k)=((U E)ᶜ.powersetCard (s-2*k)).card by rw [card_powersetCard,szU]]
    apply card_le_card_of_injOn (fun S => S \ U E)
    · intro S hs
      obtain ⟨hS,sub⟩ := mem_filter.mp hs
      exact mem_powersetCard.mpr ⟨fun x hx => mem_compl.mpr (mem_sdiff.mp hx).2,
        by rw [card_sdiff sub,(mem_powersetCard.mp hS).2,supp E he]⟩
    · intro S hs T ht eq
      have l := union_sdiff_of_subset (mem_filter.mp hs).2
      have r := union_sdiff_of_subset (mem_filter.mp ht).2
      change S \ U E=T \ U E at eq
      rw [←l,←r,eq]
  simp_rw [count]
  rw [Finset.sum_comm]
  apply (sum_le_sum (s:=P) (fun E he => extension E he)).trans
  have lp : P.card=((Fintype.card A)/2).choose k := by
    change (L.powersetCard k).card=_
    rw [card_powersetCard,show Fintype.card A/2=L.card by omega]
  simp only [sum_const,nsmul_eq_mul,lp,Nat.cast_id,le_refl]

local instance (priority := 2000) {m : Nat} : DecidableEq (Fin m) :=
  (inferInstance : LinearOrder (Fin m)).toDecidableEq

/-- Every K16 factorization admits a bisection with no fully trapped color.
At most two colors have three internal pairs on either side. -/
theorem balanced_eight (F : Factor (Fin 16) (Fin 15)) :
    ∃ S : Finset (Fin 16),S.card=8 ∧ (∀ c,Inside F c S=Inside F c Sᶜ) ∧
      (∀ c,Inside F c S≤3) ∧ (univ.filter (fun c => Inside F c S=3)).card≤2 := by
  classical
  let H := (univ : Finset (Fin 16)).powersetCard 8
  have per (c) : (∑ S∈H,(Inside F c S).choose 3) ≤ 2520 := matching_moment F c 8 3
  have avg : (∑ S∈H,∑ c,(Inside F c S).choose 3) < ∑ _∈H,3 := by
    rw [Finset.sum_comm]
    apply (sum_le_sum (fun c _ => per c)).trans_lt
    simp only [H,sum_const,nsmul_eq_mul,card_univ,Fintype.card_fin,card_powersetCard]
    decide
  obtain ⟨S,hs,small⟩ := exists_lt_of_sum_lt avg
  have sz := (mem_powersetCard.mp hs).2
  refine ⟨S,sz,?_,?_,?_⟩
  · intro c
    have eq := free_pair_size (F.invol c) (F.moving c) S
    have cap := ends_bound (F.invol c) S
    change 2*Inside F c S≤S.card at cap
    change 2*Inside F c Sᶜ=Sᶜ.card-(S.card-2*Inside F c S) at eq
    rw [card_compl,Fintype.card_fin,sz] at eq
    omega
  · intro c
    have one := single_le_sum (s:=(univ : Finset (Fin 15))) (f:=fun d => (Inside F d S).choose 3)
      (fun _ _ => Nat.zero_le _) (mem_univ c)
    change (Inside F c S).choose 3 ≤ ∑ d : Fin 15,(Inside F d S).choose 3 at one
    by_contra! large
    have b := Nat.choose_le_choose 3 (show 4≤Inside F c S by omega)
    have val : (4:Nat).choose 3=4 := by decide
    omega
  · calc
      _ = ∑ c : Fin 15, if Inside F c S=3 then 1 else 0 := (sum_boole _ _).symm
      _ ≤ ∑ c : Fin 15,(Inside F c S).choose 3 := by
        apply sum_le_sum
        intro c _
        split
        next h => rw [h]; decide
        next => exact Nat.zero_le _
      _ ≤ _ := by omega

theorem balanced_eight_coloring (g : WildExact.Coloring 16 15) :
    ∃ S : Finset (Fin 16),S.card=8 ∧ (∀ c,Inside (coloringFactor g) c S=Inside (coloringFactor g) c Sᶜ) ∧
      (∀ c,Inside (coloringFactor g) c S≤3) ∧
      (univ.filter (fun c => Inside (coloringFactor g) c S=3)).card≤2 :=
  balanced_eight (coloringFactor g)

#print axioms balanced_eight_coloring
end WildSieve
