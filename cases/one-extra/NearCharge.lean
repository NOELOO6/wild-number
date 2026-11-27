import Bounds
import Mathlib.Data.Nat.Choose.Basic

namespace WildCuts
open Finset
namespace OneExtra

def width {n : Nat} {G : Type} [DecidableEq G] (b : Blocks (Fin n) G) (i : G) :=
  (univ.filter (fun v => b.tag v=i)).card

private theorem side_count {n : Nat} {G : Type} [Fintype G] [DecidableEq G]
    (b : Blocks (Fin n) G) (U : Finset G) : (side b U).card=∑ i∈U,width b i := by
  let S := side b U
  have count := card_eq_sum_card_fiberwise (s:=S) (t:=U) (f:=b.tag)
    (fun _ hx => (mem_filter.mp hx).2)
  refine count.trans (sum_congr rfl (fun i hi => ?_))
  unfold width
  congr 1
  ext v
  simp only [S,side,mem_filter,mem_univ,true_and]
  exact ⟨And.right,fun h => ⟨h ▸ hi,h⟩⟩

private theorem matching_count {n h : Nat} (d : Blocks (Fin n) (Fin h))
    (r : Fin h) (widths : ∀ i,width d i=if i=r then 1 else 2) (s : Nat) :
    (univ.filter (fun Y : Finset (Fin h) => (side d Y).card=s)).card ≤ (h-1).choose (s/2) := by
  have size (Y : Finset (Fin h)) :
      (side d Y).card=2*(Y.erase r).card+(if r∈Y then 1 else 0) := by
    rw [side_count]
    have except : (∑ x∈Y.erase r,width d x)=(Y.erase r).card*2 :=
      sum_const_nat fun i hi => by rw [widths,if_neg (mem_erase.mp hi).1]
    by_cases inc : r∈Y
    · rw [← sum_erase_add Y (width d) inc,except,widths,if_pos rfl,if_pos inc,Nat.mul_comm]
    · simpa only [erase_eq_of_not_mem inc,if_neg inc,Nat.add_zero,Nat.mul_comm 2] using except
  let U := (univ : Finset (Fin h)).erase r
  have cardU : U.card=h-1 := by simp [U]
  rw [show (h-1).choose (s/2)=(U.powersetCard (s/2)).card by rw [card_powersetCard,cardU]]
  apply card_le_card_of_injOn (fun Y => Y.erase r)
  · intro Y hy
    have eq := (mem_filter.mp hy).2
    have sz := size Y
    refine mem_powersetCard.mpr ⟨fun x hx => mem_erase.mpr ⟨(mem_erase.mp hx).1,mem_univ _⟩,?_⟩
    split at sz <;> omega
  · intro Y hy Z hz eq
    change Y.erase r=Z.erase r at eq
    have sy := size Y
    have sz := size Z
    have ey := (mem_filter.mp hy).2
    have ez := (mem_filter.mp hz).2
    have ee := congrArg Finset.card eq
    ext x
    by_cases xr : x=r
    · subst x
      by_cases a : r∈Y <;> by_cases b : r∈Z <;> simp_all
    · simpa only [mem_erase,ne_eq,xr,not_false_eq_true,true_and] using
        (show x∈Y.erase r ↔ x∈Z.erase r by rw [eq])

def amount (n h j : Nat) :=
  Nat.fast_choose h ((3*j)/2) * ((3*j).factorial * (n-3*j).factorial)

def singleCutSum (n t h : Nat) := ∑ j∈(range (t+1)).erase 0,Nat.fast_choose t j * amount n h j

/-- Compress the sum over all sides of all matchings into one binomial sum.
The side avoiding the distinguished group consists of whole triples. -/
theorem compressed {n t h : Nat} (b : Blocks (Fin n) (Fin (t+1))) (d : Blocks (Fin n) (Fin h))
    (triples : ∀ i, i≠Fin.last t → width b i=3)
    (r : Fin h) (pairs : ∀ i,width d i=if i=r then 1 else 2) :
    (∑ u : SideName (Fin (t+1)) (Fin.last t), ∑ Y : Finset (Fin h),
        cost (side b u.val).card n (side d Y).card) ≤ singleCutSum n t (h-1) := by
  classical
  let I := SideName (Fin (t+1)) (Fin.last t)
  let J := (range (t+1)).erase 0
  let B := (univ : Finset (Fin (t+1))).erase (Fin.last t)
  have cs (u : I) : u.val⊆B := fun x hx => mem_erase.mpr ⟨fun eq => u.property.2 (eq ▸ hx),mem_univ _⟩
  have good (u : I) : u.val.card∈J := by
    have le := card_le_card (cs u)
    have sz : B.card=t := by simp [B]
    exact mem_erase.mpr ⟨(card_pos.mpr u.property.1).ne',mem_range.mpr (by omega)⟩
  have size (u : I) : (side b u.val).card=3*u.val.card := by
    rw [side_count,Nat.mul_comm]
    exact sum_const_nat fun x hx => triples _ (mem_erase.mp (cs u hx)).1
  have inner (s : Nat) : (∑ Y : Finset (Fin h),cost s n (side d Y).card) ≤
      (h-1).choose (s/2)*(s.factorial*(n-s).factorial) := by
    simp only [cost,eq_comm (a:=s),← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
    exact Nat.mul_le_mul_right _ (matching_count d r pairs _)
  have one (u : I) : (∑ Y : Finset (Fin h),cost (side b u.val).card n (side d Y).card) ≤ amount n (h-1) u.val.card := by
    rw [size u]
    simpa only [amount,← Nat.choose_eq_fast_choose] using inner (3*u.val.card)
  have groups (j) : (univ.filter (fun u : I => u.val.card=j)).card≤t.choose j := by
    have sz : B.card=t := by simp [B]
    rw [show t.choose j=(B.powersetCard j).card by rw [card_powersetCard,sz]]
    exact card_le_card_of_injOn Subtype.val
      (fun u hu => mem_powersetCard.mpr ⟨cs u,(mem_filter.mp hu).2⟩) Subtype.val_injective.injOn
  apply (sum_le_sum (s:=(univ : Finset I)) (fun u _ => one u)).trans
  rw [← sum_fiberwise_of_maps_to (fun u (_ : u∈(univ : Finset I)) => good u) (fun u => amount n (h-1) u.val.card)]
  apply sum_le_sum
  intro j _
  rw [sum_const_nat (m:=amount n (h-1) j) (fun u hu => congrArg (amount n (h-1)) (mem_filter.mp hu).2)]
  rw [← Nat.choose_eq_fast_choose]
  exact Nat.mul_le_mul_right _ (groups j)
end OneExtra
end WildCuts
