import Frame30

namespace WildSieve.Thirty.Graph
open Finset
local instance (priority := 2000) cutEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq

private theorem three : ∀ i : Fin 3,i=0 ∨ i=1 ∨ i=2 := by decide
private theorem four : ∀ i : Fin 4,i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by decide
private theorem ten : ∀ i : Fin 10,i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 := by decide

theorem signature_totals (F : Factor V C) (z : V → Fin 4) (t : Nat)
    (sizes : ∀ i,(zone z i).card=zoneSize t i) (k : Fin 10) :
    ∑ c,(signatureOf F c z).cell k = edgeTotal t k := by
  have cross (i j : Fin 4) (ne : i≠j) := sum_links F (zone z i) (zone z j) (zone_disjoint z ne)
  rcases ten k with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [signatureOf,Signature.cell] <;>
    first | rw [sum_inside,sizes]; rfl
          | rw [cross _ _ (by decide),sizes,sizes]; rfl

def selected (z : V → Fin 4) (p : Fin 4 → Bool) := (univ : Finset V).filter fun x => p (z x)

def leftMask (t : Nat) (j : Fin 4) : Bool :=
  j==2 || (j==0 && t<2) || (j==1 && t=0)
def hitMask (j : Fin 4) := decide (j.val<2)
def freeLeft (j : Fin 4) := j==2

private theorem all4 (p : Fin 4 → Prop) : (∀ j,p j) ↔ p 0 ∧ p 1 ∧ p 2 ∧ p 3 := by
  constructor
  · intro h; exact ⟨h 0,h 1,h 2,h 3⟩
  · rintro ⟨a,b,c,d⟩ j
    rcases four j with rfl|rfl|rfl|rfl <;> assumption

def matrix (s : Signature) (i j : Fin 4) : Nat :=
  match i.val,j.val with
  | 0,0 => 2*s.a | 0,1 | 1,0 => s.b | 0,2 | 2,0 => s.c | 0,3 | 3,0 => s.d
  | 1,1 => 2*s.f | 1,2 | 2,1 => s.g | 1,3 | 3,1 => s.h
  | 2,2 => 2*s.x | 2,3 | 3,2 => s.y | _,_ => 2*s.z

theorem signature_matrix (F : Factor V C) (c : C) (z : V → Fin 4) (i j : Fin 4) :
    matrix (signatureOf F c z) i j=links F c (zone z i) (zone z j) := by
  rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
    dsimp only [matrix,signatureOf,Fin.isValue,Fin.val_zero,Fin.reduceFinMk] <;>
    first | rfl | exact (links_self F c _).symm | exact links_symm F c _ _

private def closedCells (p : Fin 4 → Bool) (s : Signature) : Prop :=
  ∀ i j,p i=true → p j=false → matrix s i j=0

theorem closed_iff_cells (F : Factor V C) (c : C) (z : V → Fin 4) (p : Fin 4 → Bool) :
    Closed (F.f c) (selected z p) ↔ closedCells p (signatureOf F c z) := by
  constructor
  · intro cl i j hi hj
    rw [signature_matrix]
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_not_mem.mpr
    intro x hx
    obtain ⟨ix,jx⟩ := mem_filter.mp hx
    have a := (mem_filter.mp ix).2
    have b := (mem_filter.mp jx).2
    have inside : x∈selected z p := mem_filter.mpr ⟨mem_univ _,a ▸ hi⟩
    have seen := (mem_filter.mp (cl x inside)).2
    change p (z (F.f c x))=true at seen
    rw [b,hj] at seen
    contradiction
  · intro hc x hx
    have a := (mem_filter.mp hx).2
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    by_contra! h
    have out : p (z (F.f c x))=false := by cases v : p (z (F.f c x)) <;> simp_all
    have zero := hc (z x) (z (F.f c x)) a out
    rw [signature_matrix] at zero
    have inZone (v : V) : v∈zone z (z v) := by simp [zone]
    have yes : 0<links F c (zone z (z x)) (zone z (z (F.f c x))) :=
      card_pos.mpr ⟨x,mem_filter.mpr ⟨inZone x,inZone _⟩⟩
    omega

private theorem anchor_cells (t : Fin 3) (s : Signature) :
    closedCells (leftMask t) s ↔ anchorClosed s t=true := by
  rcases three t with rfl|rfl|rfl <;>
    simp [closedCells,all4,leftMask,anchorClosed,matrix,Nat.add_eq_zero] <;> tauto

private theorem hit_cells (s : Signature) : closedCells hitMask s ↔ labelClosed s=true := by
  simp [closedCells,all4,hitMask,labelClosed,matrix,Nat.add_eq_zero]
  tauto

private theorem complement_cells (s : Signature) : closedCells freeLeft s ↔ s.c+s.g+s.y=0 := by
  simp [closedCells,all4,freeLeft,matrix,Nat.add_eq_zero]
  tauto

theorem anchor_flag (F : Factor V C) (c : C) (z : V → Fin 4) (t : Fin 3) :
    Closed (F.f c) (selected z (leftMask t)) ↔ anchorClosed (signatureOf F c z) t=true :=
  (closed_iff_cells F c z _).trans (anchor_cells _ _)

theorem mark_flag (F : Factor V C) (c : C) (z : V → Fin 4) :
    Closed (F.f c) (selected z hitMask) ↔ labelClosed (signatureOf F c z)=true :=
  (closed_iff_cells F c z _).trans (hit_cells _)

theorem complement_flag (F : Factor V C) (c : C) (z : V → Fin 4) :
    Closed (F.f c) (selected z freeLeft) ↔
      (signatureOf F c z).c+(signatureOf F c z).g+(signatureOf F c z).y=0 :=
  (closed_iff_cells F c z _).trans (complement_cells _)

end WildSieve.Thirty.Graph
