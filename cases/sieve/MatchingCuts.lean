import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
namespace WildSieve
open Finset
variable {A : Type} [LinearOrder A]
def Closed (f : A → A) (X : Finset A) := ∀ x ∈ X, f x ∈ X

/-- One endpoint per matching edge contained in S. -/
def lowerEnds (f : A → A) (S : Finset A) := S.filter fun x => x < f x ∧ f x ∈ S

private theorem ends_disjoint {f : A → A} (ff : Function.Involutive f) (S : Finset A) :
    Disjoint (lowerEnds f S) ((lowerEnds f S).image f) := by
  apply disjoint_left.mpr
  intro x hx hi
  obtain ⟨y,hy,rfl⟩ := mem_image.mp hi
  have one := (mem_filter.mp hx).2.1
  rw [ff y] at one
  exact one.asymm (mem_filter.mp hy).2.1

theorem ends_bound {f : A → A} (ff : Function.Involutive f) (S : Finset A) :
    2*(lowerEnds f S).card ≤ S.card := by
  have sub : lowerEnds f S ∪ (lowerEnds f S).image f ⊆ S := by
    intro x hx
    rcases mem_union.mp hx with a|a
    · exact (mem_filter.mp a).1
    · obtain ⟨y,hy,rfl⟩ := mem_image.mp a
      exact (mem_filter.mp hy).2.2
  have n := card_le_card sub
  rw [card_union_of_disjoint (ends_disjoint ff S),card_image_of_injective _ ff.injective] at n
  omega

theorem recover_ends {f : A → A} (ff : Function.Involutive f) (moving : ∀ x,x ≠ f x)
    {S : Finset A} (closed : Closed f S) : lowerEnds f S ∪ (lowerEnds f S).image f=S := by
  ext x
  constructor
  · intro hx
    rcases mem_union.mp hx with h|h
    · exact (mem_filter.mp h).1
    · obtain ⟨y,hy,rfl⟩ := mem_image.mp h
      exact (mem_filter.mp hy).2.2
  · intro hx
    rcases lt_or_gt_of_ne (moving x) with lt|gt
    · exact mem_union_left _ (mem_filter.mpr ⟨hx,lt,closed x hx⟩)
    · apply mem_union_right _ (mem_image.mpr ⟨f x,?_,ff x⟩)
      exact mem_filter.mpr ⟨closed x hx,by rwa [ff x],by rwa [ff x]⟩

theorem closed_size {f : A → A} (ff : Function.Involutive f) (moving : ∀ x,x ≠ f x)
    {S : Finset A} (closed : Closed f S) : S.card=2*(lowerEnds f S).card := by
  have n := congrArg Finset.card (recover_ends ff moving closed)
  rw [card_union_of_disjoint (ends_disjoint ff S),card_image_of_injective _ ff.injective] at n
  omega

theorem lower_mono (f : A → A) {S T : Finset A} (h : S⊆T) : lowerEnds f S ⊆ lowerEnds f T := by
  intro x hx
  obtain ⟨xs,lt,fs⟩ := mem_filter.mp hx
  exact mem_filter.mpr ⟨h xs,lt,h fs⟩

/-- Partners forced outside the frozen region by the specified side D. -/
def forced (f : A → A) (B D : Finset A) := D.image f \ B

theorem strip_fixed {f : A → A} (ff : Function.Involutive f) {B D X : Finset A}
    (db : D⊆B) (dis : Disjoint X B) (closed : Closed f (D ∪ X)) :
    forced f B D ⊆ X ∧ Closed f (X \ forced f B D) := by
  have sub : forced f B D ⊆ X := by
    intro x hx
    obtain ⟨hi,nb⟩ := mem_sdiff.mp hx
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hi
    exact (mem_union.mp (closed y (mem_union_left X hy))).resolve_left (fun h => nb (db h))
  refine ⟨sub,?_⟩
  intro x hx
  obtain ⟨xx,no⟩ := mem_sdiff.mp hx
  have fx : f x ∈ X := by
    apply (mem_union.mp (closed x (mem_union_right D xx))).resolve_left
    intro h
    exact no (mem_sdiff.mpr ⟨mem_image.mpr ⟨f x,h,ff x⟩,disjoint_left.mp dis xx⟩)
  apply mem_sdiff.mpr ⟨fx,?_⟩
  intro h
  obtain ⟨y,yd,eq⟩ := mem_image.mp (mem_sdiff.mp h).1
  exact disjoint_left.mp dis xx (db (ff.injective eq ▸ yd))

/-- In a family of closed sides, the unforced part is determined by its
lower matching endpoints. -/
private theorem key_injective {f : A → A} (ff : Function.Involutive f) (moving : ∀ x,x ≠ f x)
    {S : Finset (Finset A)} {R : Finset A}
    (valid : ∀ X ∈ S,R⊆X ∧ Closed f (X \ R)) :
    Set.InjOn (fun X => lowerEnds f (X \ R)) S := by
  intro X hx Y hy eq
  have rx := recover_ends ff moving (valid X hx).2
  have ry := recover_ends ff moving (valid Y hy).2
  change lowerEnds f (X \ R)=lowerEnds f (Y \ R) at eq
  rw [eq,ry] at rx
  calc
    X = R ∪ (X \ R) := (union_sdiff_of_subset (valid X hx).1).symm
    _ = R ∪ (Y \ R) := by rw [rx]
    _ = Y := union_sdiff_of_subset (valid Y hy).1

theorem count_free {f : A → A} (ff : Function.Involutive f) (moving : ∀ x,x ≠ f x)
    (U R : Finset A) (S : Finset (Finset A)) (s : Nat)
    (valid : ∀ X ∈ S,X⊆U ∧ X.card=s ∧ R⊆X ∧ Closed f (X \ R)) :
    S.card ≤ (lowerEnds f (U \ R)).card.choose ((s-R.card)/2) := by
  rw [← card_powersetCard]
  apply card_le_card_of_injOn (fun X => lowerEnds f (X \ R)) _ (key_injective ff moving (fun x hx => (valid x hx).2.2))
  intro X hx
  obtain ⟨sub,sz,r,closed⟩ := valid X hx
  refine mem_powersetCard.mpr ⟨lower_mono f (sdiff_subset_sdiff sub (Subset.refl R)),?_⟩
  have n := closed_size ff moving closed
  rw [card_sdiff r,sz] at n
  change (lowerEnds f (X \ R)).card = _
  omega

theorem count_through_pair {f : A → A} (ff : Function.Involutive f) (moving : ∀ x,x ≠ f x)
    (U R : Finset A) (S : Finset (Finset A)) (s : Nat) (z : A)
    (valid : ∀ X ∈ S,X⊆U ∧ X.card=s ∧ R⊆X ∧ Closed f (X \ R) ∧ z∈X \ R) :
    S.card ≤ ((lowerEnds f (U \ R)).card-1).choose ((s-R.card)/2-1) := by
  classical
  by_cases empty : S=∅
  · simp [empty]
  obtain ⟨X0,h0⟩ := nonempty_iff_ne_empty.mpr empty
  let a := min z (f z)
  have core (X) (hx : X ∈ S) : a ∈ lowerEnds f (X \ R) := by
    obtain ⟨_,_,_,cl,hz⟩ := valid X hx
    rcases lt_or_gt_of_ne (moving z) with lt|gt
    · rw [show a=z from min_eq_left lt.le]
      exact mem_filter.mpr ⟨hz,lt,cl _ hz⟩
    · rw [show a=f z from min_eq_right gt.le]
      exact mem_filter.mpr ⟨cl _ hz,by rwa [ff z],by rwa [ff z]⟩
  let P := lowerEnds f (U \ R)
  have sub (X) (hx : X ∈ S) : lowerEnds f (X \ R) ⊆ P :=
    lower_mono f (sdiff_subset_sdiff (valid X hx).1 (Subset.refl R))
  have ap := sub X0 h0 (core X0 h0)
  rw [← card_erase_of_mem ap,← card_powersetCard]
  apply card_le_card_of_injOn (fun X => (lowerEnds f (X \ R)).erase a)
  · intro X hx
    refine mem_powersetCard.mpr ⟨erase_subset_erase _ (sub X hx),?_⟩
    obtain ⟨_,sz,rs,cl,_⟩ := valid X hx
    have n := closed_size ff moving cl
    rw [card_sdiff rs,sz] at n
    rw [card_erase_of_mem (core X hx)]
    omega
  · intro X hx Y hy eq
    apply key_injective ff moving (fun x hx => ⟨(valid x hx).2.2.1,(valid x hx).2.2.2.1⟩) hx hy
    have added := congrArg (insert a) eq
    simpa [insert_erase (core X hx),insert_erase (core Y hy)] using added
end WildSieve
