import Mathlib.Algebra.Group.Fin.Basic
import RotationalLayouts
import Extract21
import Cyclic21Check

namespace Wild21
open Finset EdgeWalk WildExact WildDeletion
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

private def rep (z : V) : V := ⟨z.val%3,by have := Nat.mod_lt z.val (by decide : 0<3); omega⟩

private theorem rep_mem (z : V) : rep z∈([0,1,2] : List V) := by revert z; decide

/-- Translation by a multiple of three permutes the seven triple stars. -/
private theorem layout_facts : layouts.all (fun w => w.length==14 &&
    w.all (fun e => e.1 != e.2) && (List.finRange 21).all (fun z =>
      (shift w (z-rep z)).all (fun e => w.contains e))) = true := by native_decide

/-- Every rotational minimum coloring of K21 admits fourteen wild edges.
The cycles of vertices and colors may have arbitrary labels. -/
theorem exact_cyclic_K21 (g : Coloring 21 21) (v : V ≃ V) (rot : Cyclic g v) : Exact g 14 := by
  obtain ⟨s,ok,zero⟩ := find_starter g v rot acceptsStarter every_starter_passes
  obtain ⟨w,hw,win⟩ := List.any_eq_true.mp ok
  obtain ⟨info,shifted⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp layout_facts w hw)
  obtain ⟨sz,ne⟩ := Bool.and_eq_true_iff.mp info
  apply exact_of_upper _ (fun _ => odd_lower (by decide) g)
  apply Rotation.upper_of_layout g (by decide) v rot [0,1,2] rep rep_mem s w zero
    (beq_iff_eq.mp sz).le (fun e he => bne_iff_ne.mp (List.all_eq_true.mp ne e he)) _ win
  intro z e he
  have all := List.all_eq_true.mp shifted z (List.mem_finRange z)
  simpa using List.all_eq_true.mp all e he

/-- The same value holds for any K22 coloring with a cyclic deletion. -/
theorem exact_cyclic_deletion_K22 (g : Coloring 22 21) (v : V ≃ V)
    (rot : Cyclic (restrict g) v) : Exact g 14 := by
  obtain ⟨⟨w,legal,sz,win⟩,_⟩ := exact_cyclic_K21 (restrict g) v rot
  exact exact_of_upper (upper_from_deletion g ⟨w,legal,sz.le,win⟩)
    (fun _ => even_lower (by decide) g)

#print axioms exact_cyclic_K21
#print axioms exact_cyclic_deletion_K22
end Wild21
