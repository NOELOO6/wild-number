import FrameCuts30
import MatchingSpectrum

namespace WildSieve.Thirty.Graph
open Finset
local instance (priority := 2000) spectrumEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq

/-- Upper triangular cell index for a matching edge between two regions. -/
def cellCode (i j : Fin 4) : Fin 10 :=
  match i.val,j.val with
  | 0,0 => 0 | 0,1 | 1,0 => 1 | 0,2 | 2,0 => 2 | 0,3 | 3,0 => 3
  | 1,1 => 4 | 1,2 | 2,1 => 5 | 1,3 | 3,1 => 6
  | 2,2 => 7 | 2,3 | 3,2 => 8 | _,_ => 9

def ends (h : Fin 10) : Multiset (Fin 4) :=
  match h.val with
  | 0 => {0,0} | 1 => {0,1} | 2 => {0,2} | 3 => {0,3} | 4 => {1,1}
  | 5 => {1,2} | 6 => {1,3} | 7 => {2,2} | 8 => {2,3} | _ => {3,3}

private theorem symmetric_code : ∀ i j,cellCode i j=cellCode j i := by decide
private theorem ends_code : ∀ i j,ends (cellCode i j)={i,j} := by decide

def cellList (s : Signature) : List (Fin 10) :=
  (List.finRange 10).flatMap fun (i : Fin 10) => List.replicate (s.cell i.val) i

private theorem list_counts (s : Signature) (k : Fin 10) :
    (cellList s : Multiset (Fin 10)).count k=s.cell k := by
  simp only [cellList,Multiset.coe_count]
  have tally (l : List (Fin 10)) :
      (l.flatMap (fun (i : Fin 10) => List.replicate (s.cell i.val) i)).count k =
      ((l.filter (·=k)).length)*(s.cell k) := by
    induction l with
    | nil => simp
    | cons i l ih => by_cases h : i=k <;> simp [List.count_replicate,h,ih,Ne.symm, Nat.add_mul,Nat.mul_add,Nat.add_comm]
  rw [tally]
  have once : ∀ a : Fin 10,((List.finRange 10).filter (·=a)).length=1 := by decide
  rw [once,one_mul]

private theorem sum_matrix (s : Signature) (k : Fin 10) :
    (∑ i : Fin 4,∑ j : Fin 4,if cellCode i j=k then matrix s i j else 0)=2*s.cell k := by
  have all : ∀ j : Fin 10,j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by decide
  rcases all k with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [Fin.sum_univ_four,cellCode,matrix,Signature.cell] <;> omega

private theorem link_row (F : Factor V C) (c : C) (z : V → Fin 4) (i j : Fin 4) :
    links F c (zone z i) (zone z j)=
      ∑ x : V,if i=z x then (if j=z (F.f c x) then 1 else 0) else 0 := by
  simp only [links,zone,Finset.card_filter,sum_filter,mem_filter,mem_univ,true_and]
  apply sum_congr rfl
  intro x _
  by_cases a : i=z x <;> by_cases b : j=z (F.f c x) <;> simp [a,b,eq_comm]

private theorem all_vertices (F : Factor V C) (c : C) (z : V → Fin 4) (k : Fin 10) :
    ((univ : Finset V).filter (fun x => cellCode (z x) (z (F.f c x))=k)).card =
      2*(signatureOf F c z).cell k := by
  have eq := sum_matrix (signatureOf F c z) k
  simp_rw [signature_matrix] at eq
  rw [←eq,Finset.card_filter]
  have per (i j : Fin 4) : (if cellCode i j=k then links F c (zone z i) (zone z j) else 0) =
      ∑ x : V, if i=z x then (if j=z (F.f c x) then (if cellCode i j=k then 1 else 0) else 0) else 0 := by
    by_cases same : cellCode i j=k <;> simp [same,link_row]
  simp_rw [per]
  have switch (g : Fin 4 → Fin 4 → V → Nat) :
      (∑ i,∑ j,∑ x,g i j x)=∑ x,∑ i,∑ j,g i j x := by
    calc _ = ∑ i,∑ x,∑ j,g i j x := sum_congr rfl (fun _ _ => sum_comm)
         _ = _ := sum_comm
  rw [switch]
  apply sum_congr rfl
  intro x _
  simp

theorem edge_inventory (F : Factor V C) (c : C) (z : V → Fin 4) :
    (lowerEnds (F.f c) univ).val.map (fun x => cellCode (z x) (z (F.f c x))) =
      (cellList (signatureOf F c z) : Multiset (Fin 10)) := by
  classical
  let f := F.f c
  let tag (x : V) := cellCode (z x) (z (f x))
  apply Multiset.ext.mpr
  intro k
  let U := (univ : Finset V).filter (fun x => tag x=k)
  have cl : Closed f U := by
    intro x hx
    have h := (mem_filter.mp hx).2
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    change cellCode (z (f x)) (z (f (f x)))=k
    rw [show f (f x)=x from F.invol c x,symmetric_code]
    exact h
  have size := closed_size (F.invol c) (F.moving c) cl
  have eq : lowerEnds f U=(lowerEnds f univ).filter (fun x => tag x=k) := by
    ext x
    simp only [lowerEnds,U,mem_filter,mem_univ,true_and,and_true]
    constructor
    · rintro ⟨a,b,_⟩; exact ⟨b,a⟩
    · rintro ⟨b,a⟩
      exact ⟨a,b,(mem_filter.mp (cl x (mem_filter.mpr ⟨mem_univ _,a⟩))).2⟩
  rw [eq] at size
  have total := all_vertices F c z k
  change U.card=_ at total
  rw [list_counts,Multiset.count_map]
  change ((lowerEnds f univ).val.filter (fun x => k=tag x)).card=_
  change ((lowerEnds f univ).filter (fun x => k=tag x)).card=_
  have flip : (lowerEnds f univ).filter (fun x => k=tag x) =
      (lowerEnds f univ).filter (fun x => tag x=k) := filter_congr (fun _ _ => eq_comm)
  rw [flip]
  omega

/-- The zone profile distribution of all closed 2k-sets is exactly the finite
selection distribution of the upper-triangular cell inventory. -/
theorem cell_spectrum (F : Factor V C) (c : C) (z : V → Fin 4) (k : Nat) :
    (candidates F c ∅ univ (2*k)).val.map (fun Q => Q.val.map z) =
      ((((cellList (signatureOf F c z) : Multiset (Fin 10)).map ends).powersetCard k).map Multiset.sum) := by
  rw [matching_spectrum,←edge_inventory F c z,Multiset.map_map]
  congr 2
  apply Multiset.map_congr rfl
  intro x _
  exact (ends_code _ _).symm

end WildSieve.Thirty.Graph
