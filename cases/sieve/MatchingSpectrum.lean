import MatchingSixes
import Mathlib.Data.Multiset.Powerset
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

namespace WildSieve
open Finset
variable {A C B : Type} [LinearOrder A]

def pairUnion (f : A → A) (I : Finset A) := I∪I.image f

theorem closed_pair_images (F : Factor A C) (c : C) (U : Finset A) (k : Nat) :
    candidates F c ∅ U (2*k)=((lowerEnds (F.f c) U).powersetCard k).image (pairUnion (F.f c)) := by
  ext Q
  constructor
  · intro h
    obtain ⟨sub,sz,cl⟩ := candidate_mem.mp h
    simp only [empty_union] at cl
    have n := closed_size (F.invol c) (F.moving c) cl
    exact mem_image.mpr ⟨lowerEnds (F.f c) Q,mem_powersetCard.mpr ⟨lower_mono _ sub,by omega⟩,
      recover_ends (F.invol c) (F.moving c) cl⟩
  · intro h
    obtain ⟨I,hi,rfl⟩ := mem_image.mp h
    obtain ⟨sub,sz⟩ := mem_powersetCard.mp hi
    obtain ⟨u,n,cl,_⟩ := close_lowers F c sub
    exact candidate_mem.mpr ⟨u,by simpa only [pairUnion,sz] using n,by simpa only [empty_union] using cl⟩

private theorem pairUnion_inj (F : Factor A C) (c : C) (U : Finset A) (k : Nat) :
    Set.InjOn (pairUnion (F.f c)) ((lowerEnds (F.f c) U).powersetCard k) := by
  intro I hi J hj eq
  have i := (close_lowers F c (mem_powersetCard.mp hi).1).2.2.2
  have j := (close_lowers F c (mem_powersetCard.mp hj).1).2.2.2
  exact i.symm.trans ((congrArg (lowerEnds (F.f c)) eq).trans j)

def pairTag (f : A → A) (tag : A → B) (x : A) : Multiset B := {tag x,tag (f x)}

private theorem endpoint_sum (F : Factor A C) (c : C) (U : Finset A) (I : Finset A)
    (sub : I⊆lowerEnds (F.f c) U) (z : A → B) :
    (pairUnion (F.f c) I).val.map z = (I.val.map (pairTag (F.f c) z)).sum := by
  classical
  have apart : Disjoint I (I.image (F.f c)) := by
    apply disjoint_left.mpr
    intro x hx im
    obtain ⟨y,hy,rfl⟩ := mem_image.mp im
    have lt := (mem_filter.mp (sub hx)).2.1
    rw [F.invol c y] at lt
    exact lt.asymm (mem_filter.mp (sub hy)).2.1
  rw [pairUnion,←Finset.disjUnion_eq_union I _ apart]
  change (I.val+(I.image (F.f c)).val).map z=_
  rw [image_val_of_injOn (F.invol c).injective.injOn,Multiset.map_add,Multiset.map_map]
  generalize I.val=M
  induction M using Multiset.induction with
  | empty => simp
  | cons x l ih =>
    simp only [Multiset.map_cons,Multiset.sum_cons]
    rw [←ih]
    simp [pairTag,Multiset.cons_swap]

/-- Push the actual list of all closed sets of size 2k to its region
occupancies. The right side depends only on the multiset of single-edge types. -/
theorem matching_spectrum (F : Factor A C) (c : C) (U : Finset A) (k : Nat) (z : A → B) :
    (candidates F c ∅ U (2*k)).val.map (fun Q => Q.val.map z) =
      (((lowerEnds (F.f c) U).val.map (pairTag (F.f c) z)).powersetCard k).map Multiset.sum := by
  classical
  rw [closed_pair_images,image_val_of_injOn (pairUnion_inj F c U k),
    Multiset.powersetCard_map,←Finset.map_val_val_powersetCard]
  simp only [Multiset.map_map]
  apply Multiset.map_congr rfl
  intro I hi
  exact endpoint_sum F c U I (mem_powersetCard.mp hi).1 z

end WildSieve
