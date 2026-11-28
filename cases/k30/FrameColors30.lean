import FrameIncidence30

namespace WildSieve.Thirty.Graph
open Finset
local instance (priority := 2000) colorEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq
set_option maxRecDepth 10000

theorem internal_count (F : Factor V C) (c : C) (z : V → Fin 4) (t : Fin 3) :
    internal (signatureOf F c z) t=Inside F c (selected z (leftMask t)) := by
  let A := zone z 0
  let B := zone z 1
  let L := zone z 2
  have dAB : Disjoint A B := zone_disjoint z (by decide)
  have dAL : Disjoint A L := zone_disjoint z (by decide)
  have dBL : Disjoint B L := zone_disjoint z (by decide)
  have description : ∀ j : Fin 3,selected z (leftMask j)=
      (if j.val=0 then A∪B∪L else if j.val=1 then A∪L else L) := by
    intro j
    ext v
    have three : ∀ i : Fin 3,i=0 ∨ i=1 ∨ i=2 := by decide
    have four : ∀ i : Fin 4,i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by decide
    rcases three j with rfl|rfl|rfl <;> rcases four (z v) with h|h|h|h <;>
      simp [selected,leftMask,A,B,L,zone,h]
  rw [description]
  have three : ∀ i : Fin 3,i=0 ∨ i=1 ∨ i=2 := by decide
  rcases three t with rfl|rfl|rfl
  · change _=Inside F c ((A∪B)∪L)
    rw [inside_union F c _ _ (disjoint_union_left.mpr ⟨dAL,dBL⟩),inside_union F c _ _ dAB,
      links_symm F c (A∪B) L,links_union F c L A B dAB,links_symm F c L A,links_symm F c L B]
    change Inside F c A+links F c A B+links F c A L+Inside F c B+links F c B L+Inside F c L=_
    omega
  · exact (inside_union F c A L dAL).symm
  · rfl

/-- Four-region color counts for each individual compatible pair of triples. -/
theorem frame_colors (F : Factor V C) (L : Finset V) (l : L.card=12) (a : C) (cl : Closed (F.f a) L)
    (t : Fin 3) (P : Pattern) (hp : P∈frames F L t) :
    let z := regionOf F L t P
    (∀ c,signatureOf F c z∈signatures t) ∧
    (∀ k : Fin 10,∑ c,(signatureOf F c z).cell k=edgeTotal t k) ∧
    (1≤((univ : Finset C).filter fun c => anchorClosed (signatureOf F c z) t).card) ∧
    (∀ c,internal (signatureOf F c z) t=Inside F c L) ∧
    (∀ c,labelClosed (signatureOf F c z)=true ↔ c∈owners F (vertices P)) := by
  let z := regionOf F L t P
  have spec := region_spec F L l t P hp
  refine ⟨fun c => mem_signatures (signature_fits F c z t spec.sizes),
    signature_totals F z t spec.sizes,?_,?_,?_⟩
  · exact card_pos.mpr ⟨a,mem_filter.mpr ⟨mem_univ _,(anchor_flag F a z t).mp (spec.left.symm ▸ cl)⟩⟩
  · intro c
    rw [internal_count,spec.left]
  · intro c
    rw [←mark_flag,spec.mark,owner_mem]

end WildSieve.Thirty.Graph
