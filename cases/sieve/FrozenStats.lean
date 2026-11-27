import Factors
namespace WildSieve
open Finset
variable {A C : Type} [LinearOrder A]
def paired (f : A → A) (S : Finset A) := S.filter fun x => f x ∈ S

theorem paired_size {f : A → A} (ff : Function.Involutive f) (moving : ∀ x,x≠f x)
    (S : Finset A) : (paired f S).card=2*(lowerEnds f S).card := by
  have cl : Closed f (paired f S) := by
    intro x hx
    obtain ⟨xs,fx⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨fx,by rwa [ff x]⟩
  have low : lowerEnds f (paired f S) = lowerEnds f S := by
    ext x
    simp [paired,lowerEnds,ff x,and_assoc,and_left_comm,and_comm]
  rw [closed_size ff moving cl,low]

theorem image_inter {f : A → A} (ff : Function.Involutive f) (S : Finset A) :
    S.image f ∩ S=paired f S := by
  ext x
  constructor
  · intro h
    obtain ⟨im,xs⟩ := mem_inter.mp h
    obtain ⟨y,ys,rfl⟩ := mem_image.mp im
    exact mem_filter.mpr ⟨xs,by rwa [ff y]⟩
  · intro h
    obtain ⟨xs,fx⟩ := mem_filter.mp h
    exact mem_inter.mpr ⟨mem_image.mpr ⟨f x,fx,ff x⟩,xs⟩

theorem external_size {f : A → A} (ff : Function.Involutive f) (moving : ∀ x,x≠f x)
    (S : Finset A) : (forced f S S).card = S.card-2*(lowerEnds f S).card := by
  have n := Finset.card_sdiff_add_card_inter (S.image f) S
  rw [image_inter ff,paired_size ff moving,card_image_of_injective _ ff.injective] at n
  change (S.image f \ S).card = _
  omega

theorem free_pair_size [Fintype A] {f : A → A} (ff : Function.Involutive f) (moving : ∀ x,x≠f x)
    (B : Finset A) :
    2*(lowerEnds f Bᶜ).card = Bᶜ.card - (B.card-2*(lowerEnds f B).card) := by
  have partition : paired f Bᶜ = Bᶜ \ forced f B B := by
    ext x
    simp only [paired,mem_filter,mem_compl,forced,mem_sdiff,mem_image]
    constructor
    · rintro ⟨nx,nf⟩
      exact ⟨nx,fun ⟨⟨y,hy,eq⟩,_⟩ => nf ((eq ▸ ff y).symm ▸ hy)⟩
    · rintro ⟨nx,h⟩
      exact ⟨nx,fun fb => h ⟨⟨f x,fb,ff x⟩,nx⟩⟩
  have sub : forced f B B ⊆ Bᶜ := fun _ h => mem_compl.mpr (mem_sdiff.mp h).2
  rw [← paired_size ff moving,partition,card_sdiff sub,external_size ff moving]

/-- A realizable cut cannot contain just one endpoint of an edge lying in
the frozen region. Its external partners are precisely those of D outside D. -/
theorem no_frozen_cross {f : A → A} {B D X : Finset A} (dis : Disjoint X B)
    (cl : Closed f (D ∪ X)) (x : A) (xd : x∈D) (fb : f x∈B) : f x∈D :=
  (mem_union.mp (cl x (mem_union_left X xd))).resolve_right (fun fx => disjoint_left.mp dis fx fb)

theorem forced_eq_external {f : A → A} {B D X : Finset A} (db : D⊆B)
    (dis : Disjoint X B) (cl : Closed f (D ∪ X)) : forced f B D = forced f D D := by
  ext x
  constructor
  · intro h
    obtain ⟨a,b⟩ := mem_sdiff.mp h
    exact mem_sdiff.mpr ⟨a,fun xd => b (db xd)⟩
  · intro h
    obtain ⟨im,nd⟩ := mem_sdiff.mp h
    obtain ⟨y,yd,rfl⟩ := mem_image.mp im
    exact mem_sdiff.mpr ⟨mem_image.mpr ⟨y,yd,rfl⟩,fun fb => nd (no_frozen_cross dis cl y yd fb)⟩

theorem split_inside (F : Factor A C) (c : C) {B D X : Finset A} (db : D⊆B)
    (dis : Disjoint X B) (cl : Closed (F.f c) (D ∪ X)) :
    Inside F c B=Inside F c D+Inside F c (B \ D) := by
  let f := F.f c
  have parts : lowerEnds f B = lowerEnds f D ∪ lowerEnds f (B \ D) := by
    ext x
    constructor
    · intro hx
      obtain ⟨xb,lt,fxb⟩ := mem_filter.mp hx
      by_cases xd : x∈D
      · exact mem_union_left _ (mem_filter.mpr ⟨xd,lt,no_frozen_cross dis cl x xd fxb⟩)
      · have fy : f x ∉ D := by
          intro d
          have eq := F.invol c x
          have inB : F.f c (f x) ∈ B := by simpa [f,eq] using xb
          have inD := no_frozen_cross dis cl (f x) d inB
          exact xd (by simpa [f,eq] using inD)
        exact mem_union_right _ (mem_filter.mpr ⟨mem_sdiff.mpr ⟨xb,xd⟩,lt,mem_sdiff.mpr ⟨fxb,fy⟩⟩)
    · rintro h
      rcases mem_union.mp h with h|h
      · exact lower_mono f db h
      · exact lower_mono f sdiff_subset h
  have nonoverlap : Disjoint (lowerEnds f D) (lowerEnds f (B \ D)) :=
    disjoint_sdiff.mono (filter_subset _ _) (filter_subset _ _)
  unfold Inside
  change (lowerEnds f B).card = _
  rw [parts,card_union_of_disjoint nonoverlap]
end WildSieve
