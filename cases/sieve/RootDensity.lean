import TripleDensity
import ValidTriples

namespace WildSieve.RootDensity
open Finset TripleIncidence WildExact WildExact.TripleRepair
variable {n : Nat}
local instance (priority := 2000) rootDensityEq : DecidableEq (Fin n) := (inferInstance : LinearOrder (Fin n)).toDecidableEq

noncomputable def sealed (g : Coloring n n) : Finset (Finset (Fin n)) := by
  classical exact univ.filter (SealedTriple g)

theorem mem_sealed {g : Coloring n n} {A : Finset (Fin n)} : A∈sealed g ↔ SealedTriple g A := by
  classical simp [sealed]

theorem pair_bound (g : Coloring n n) (odd : n%2=1) : PairBound (sealed g) 3 := by
  classical
  intro P size
  obtain ⟨x,y,xy,rfl⟩ := card_eq_two.mp size
  let Z := univ.filter fun z => SealedTriple g {x,y,z}
  have lift : throughPair (sealed g) {x,y}⊆Z.image (fun z => {x,y,z}) := by
    intro T hT
    obtain ⟨yes,sub⟩ := mem_filter.mp hT
    have e : (T \ {x,y}).card=1 := by rw [card_sdiff sub,(mem_sealed.mp yes).1];simp [xy]
    obtain ⟨z,one⟩ := card_eq_one.mp e
    have back := union_sdiff_of_subset sub
    rw [one] at back
    have eq : ({x,y,z} : Finset (Fin n))=T := by simpa [insert_union] using back
    exact mem_image.mpr ⟨z,mem_filter.mpr ⟨mem_univ _,eq ▸ mem_sealed.mp yes⟩,eq⟩
  apply (card_le_card lift).trans (card_image_le.trans ?_)
  convert sealed_degree g odd x y xy using 2
  ext z
  simp only [Z,mem_filter,mem_univ,true_and]
  apply Iff.of_eq
  congr 1
  ext v
  simp

def bound (t h : Nat) :=
  let n := 3*t
  let p := h*(h+2)-(h*(3*(3*(n-1)/2)))
  let saving := 3*ways (t-2)-(n-6).choose 2*ways (t-3)
  (6*ways t+p*saving-6*(h*ways (t-1))+5)/6

theorem lower (g : Coloring n n) (odd : n%2=1) (t : Nat) (order : n=3*t)
    (cost : (n-6).choose 2*ways (t-3) ≤ 3*ways (t-2)) :
    bound t (sealed g).card ≤ (clear (sealed g)).card := by
  have size (A) (h : A∈sealed g) := (mem_sealed.mp h).1
  obtain ⟨p,lo,hi⟩ := density_budget t 3 order (sealed g) size (pair_bound g odd)
  rw [show 3*(n-6).choose 2/3=(n-6).choose 2 by omega] at hi
  let h := (sealed g).card
  let b := h*(h+2)-h*(3*(3*(n-1)/2))
  let s := 3*ways (t-2)-(n-6).choose 2*ways (t-3)
  have fit : b≤p := by dsimp [b,h];omega
  have a := Nat.mul_le_mul_right s fit
  have e : 3*ways (t-2)=s+(n-6).choose 2*ways (t-3) := by dsimp [s];omega
  rw [e,Nat.mul_add] at hi
  change (6*ways t+(h*(h+2)-h*(3*(3*(3*t-1)/2)))*
    (3*ways (t-2)-(3*t-6).choose 2*ways (t-3))-6*(h*ways (t-1))+5)/6≤_
  rw [←order]
  change (6*ways t+b*s-6*(h*ways (t-1))+5)/6≤_
  dsimp only [h] at *
  omega

/-- The table covers every odd multiple of three from 15 through 75.
Each entry counts unordered partitions clearing all single-block cuts. -/
def orders := [5,7,9,11,13,15,17,19,21,23,25]

def minimum (t : Nat) := bound t ((3*t).choose 2)

private theorem checked : orders.all (fun t =>
    decide (((3*t-6).choose 2*ways (t-3)) ≤ 3*ways (t-2)) &&
    (List.range ((3*t).choose 2+1)).all (fun h => decide (minimum t≤bound t h)))=true := by
  native_decide

theorem surviving (g : Coloring n n) (odd : n%2=1) (t : Nat) (order : n=3*t) (listed : t∈orders) :
    minimum t≤(clear (sealed g)).card := by
  classical
  have ⟨cost,rows⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp checked t listed)
  have cap := within_bound (sealed g) (fun _ h => (mem_sealed.mp h).1) 3 (pair_bound g odd) univ
  have all : within (sealed g) univ=sealed g := by ext; simp [within]
  rw [all,card_univ,Fintype.card_fin] at cap
  have num : n.choose 2=(3*t).choose 2 := congrArg (fun i : Nat => i.choose 2) order
  rw [num] at cap
  apply le_trans (of_decide_eq_true (List.all_eq_true.mp rows (sealed g).card (List.mem_range.mpr (by omega))))
  exact lower g odd t order (order ▸ of_decide_eq_true cost)

/-- Every K15 coloring has at least 154,000 unordered five-triple
partitions with an outgoing edge of every color in every block. -/
theorem fifteen (g : Coloring 15 15) : 154000≤(clear (sealed g)).card := by
  simpa only [show minimum 5=154000 by decide] using surviving g (by decide) 5 rfl (by decide)

#print axioms fifteen
end WildSieve.RootDensity
