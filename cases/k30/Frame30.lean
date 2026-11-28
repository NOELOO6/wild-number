import GraphPopulation30
import JointDegrees
import Signature30
import Mathlib.Algebra.BigOperators.Fin

namespace WildSieve.Thirty.Graph
open Finset
local instance (priority := 2000) frameEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq

/-- Directed matching edges from A into B. At distinct disjoint regions,
each matching edge in the cell has one orientation from A to B. -/
def links (F : Factor V C) (c : C) (A B : Finset V) : Nat :=
  (A.filter fun x => F.f c x∈B).card

theorem links_symm (F : Factor V C) (c : C) (A B : Finset V) : links F c A B=links F c B A := by
  let f := F.f c
  have pairs : (A.filter fun x => f x∈B).image f = B.filter (fun x => f x∈A) := by
    ext y
    constructor
    · intro h
      obtain ⟨x,hx,rfl⟩ := mem_image.mp h
      exact mem_filter.mpr ⟨(mem_filter.mp hx).2,by simpa only [f,F.invol c x] using (mem_filter.mp hx).1⟩
    · intro h
      obtain ⟨b,a⟩ := mem_filter.mp h
      exact mem_image.mpr ⟨f y,mem_filter.mpr ⟨a,by simpa only [f,F.invol c y] using b⟩,F.invol c y⟩
  exact (card_image_of_injective _ (F.invol c).injective).symm.trans (congrArg card pairs)

theorem links_self (F : Factor V C) (c : C) (A : Finset V) : links F c A A=2*Inside F c A :=
  paired_size (F.invol c) (F.moving c) A

theorem links_union (F : Factor V C) (c : C) (A B D : Finset V) (bd : Disjoint B D) :
    links F c A (B∪D)=links F c A B+links F c A D := by
  have eq : A.filter (fun x => F.f c x∈B∪D)=
      (A.filter fun x => F.f c x∈B)∪(A.filter fun x => F.f c x∈D) := by
    ext x; simp [and_or_left]
  have sep : Disjoint (A.filter fun x => F.f c x∈B) (A.filter fun x => F.f c x∈D) :=
    disjoint_left.mpr (fun _ x y => disjoint_left.mp bd (mem_filter.mp x).2 (mem_filter.mp y).2)
  exact (congrArg card eq).trans (card_union_of_disjoint sep)

theorem inside_union (F : Factor V C) (c : C) (A B : Finset V) (ab : Disjoint A B) :
    Inside F c (A∪B)=Inside F c A+links F c A B+Inside F c B := by
  have eq := links_union F c (A∪B) A B ab
  rw [links_self,links_symm F c (A∪B) A,links_symm F c (A∪B) B,
    links_union F c A A B ab,links_union F c B A B ab,links_self,links_self,links_symm F c B A] at eq
  omega

theorem sum_links (F : Factor V C) (A B : Finset V) (ab : Disjoint A B) :
    ∑ c, links F c A B=A.card*B.card := by
  classical
  have per (x : V) (hx : x∈A) :
      ((univ : Finset C).filter fun c => F.f c x∈B).card=B.card := by
    have outside : x∉B := fun h => disjoint_left.mp ab hx h
    simpa only [into,erase_eq_of_not_mem outside] using into_size F x B
  simp only [links,Finset.card_filter]
  rw [sum_comm]
  simp_rw [←Finset.card_filter]
  rw [sum_congr rfl per,sum_const,nsmul_eq_mul,Nat.cast_id]

def zone (region : V → Fin 4) (i : Fin 4) := (univ : Finset V).filter fun x => region x=i

theorem zone_disjoint (z : V → Fin 4) {i j : Fin 4} (ne : i≠j) :
    Disjoint (zone z i) (zone z j) :=
  disjoint_left.mpr (fun _ hi hj => ne ((mem_filter.mp hi).2.symm.trans (mem_filter.mp hj).2))

def signatureOf (F : Factor V C) (c : C) (z : V → Fin 4) : Signature :=
  let s := zone z
  let l (i j) := links F c (s i) (s j)
  ⟨Inside F c (s 0), l 0 1,l 0 2,l 0 3,Inside F c (s 1),l 1 2,l 1 3,
      Inside F c (s 2),l 2 3,Inside F c (s 3)⟩

def zoneSize (t : Nat) (i : Fin 4) :=
  match i.val with | 0 | 1 => 3 | 2 => leftFree t | _ => 24-leftFree t

private theorem zone_row (F : Factor V C) (c : C) (z : V → Fin 4) (i : Fin 4) :
    (∑ j,links F c (zone z i) (zone z j))=(zone z i).card := by
  simp only [links,Finset.card_filter]
  rw [sum_comm]
  simp [zone]

theorem signature_fits (F : Factor V C) (c : C) (z : V → Fin 4) (t : Nat)
    (sizes : ∀ i,(zone z i).card=zoneSize t i) : Fits t (signatureOf F c z) := by
  have row (i : Fin 4) := (zone_row F c z i).trans (sizes i)
  have a := row 0
  have b := row 1
  have l := row 2
  have r := row 3
  simp only [Fin.sum_univ_four,links_self] at a b l r
  rw [links_symm F c (zone z 1) (zone z 0)] at b
  rw [links_symm F c (zone z 2) (zone z 0),links_symm F c (zone z 2) (zone z 1)] at l
  rw [links_symm F c (zone z 3) (zone z 0),links_symm F c (zone z 3) (zone z 1),
    links_symm F c (zone z 3) (zone z 2)] at r
  exact ⟨a,b,l,r⟩

end WildSieve.Thirty.Graph
