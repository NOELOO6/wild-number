import Mathlib.Algebra.Group.Fin.Basic
import OrbitLayouts
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
  let line (e : Edge 21) := (min (v e.1) (v e.2),max (v e.1) (v e.2))
  let W := w.toFinset.image line
  have stepW (a b : V) (ab : (a,b)∈w) : Touch W (v a) (v b) := by
    have h : line (a,b)∈W := mem_image_of_mem line (List.mem_toFinset.mpr ab)
    rcases le_total (v a) (v b) with l|l
    · exact Or.inl (by simpa [line,l] using h)
    · exact Or.inr (by simpa [line,l] using h)
  apply exact_of_upper _ (fun _ => odd_lower (by decide) g)
  refine ⟨W,?_,?_,?_⟩
  · intro e he
    obtain ⟨p,hp,rfl⟩ := mem_image.mp he
    have nv : v p.1≠v p.2 := fun eq => (bne_iff_ne.mp (List.all_eq_true.mp ne p (List.mem_toFinset.mp hp))) (v.injective eq)
    rcases lt_or_gt_of_ne nv with l|l <;> simp [line,l,l.le]
  · exact card_image_le.trans (w.toFinset_card_le.trans (beq_iff_eq.mp sz).le)
  let I := {i : V // i∈([0,1,2] : List V)}
  apply works_of_walk_cover (I:=I) (fun i => Adj (w++shift s i.val))
    (fun i => connected_of_passes 0 _ (List.all_eq_true.mp win _ i.property))
  intro c
  obtain ⟨u,hu⟩ := (Finite.injective_iff_surjective.mp (missing_injective (by decide : 21%2=1) g)) c
  let z := v.symm u
  let t := z-rep z
  have rt : rep z+t=z := by dsimp [t]; rw [add_comm,sub_add_cancel]
  have col : missingColor g (v z)=c := by simpa [z] using hu
  refine ⟨⟨rep z,rep_mem z⟩,fun x => v (x+t),fun y => ⟨v.symm y-t,by simp⟩,?_⟩
  have one (x y : V) (h : (x,y)∈w++shift s (rep z)) : Joined g W c (v (x+t)) (v (y+t)) := by
    rcases List.mem_append.mp h with hw'|hc
    · have mem : (x+t,y+t)∈shift w t := List.mem_map.mpr ⟨(x,y),hw',rfl⟩
      have all := List.all_eq_true.mp shifted z (List.mem_finRange z)
      exact Or.inl (stepW _ _ (by simpa using List.all_eq_true.mp all _ mem))
    · obtain ⟨⟨a,b⟩,baseEdge,eq⟩ := List.mem_map.mp hc
      change (a+rep z,b+rep z)=(x,y) at eq
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
      obtain ⟨ab,paint⟩ := zero _ baseEdge
      have edge := rot a b z ab paint
      refine Or.inr ⟨?_,?_⟩
      · exact fun eq => ab (add_right_cancel (add_right_cancel (v.injective eq)))
      · simpa only [add_assoc,rt] using edge.trans col
  intro x y e
  exact e.elim (one x y) (fun h => joined_symm g (one y x h))

/-- The same value holds for any K22 coloring with a cyclic deletion. -/
theorem exact_cyclic_deletion_K22 (g : Coloring 22 21) (v : V ≃ V)
    (rot : Cyclic (restrict g) v) : Exact g 14 := by
  obtain ⟨⟨w,legal,sz,win⟩,_⟩ := exact_cyclic_K21 (restrict g) v rot
  exact exact_of_upper (upper_from_deletion g ⟨w,legal,sz.le,win⟩)
    (fun _ => even_lower (by decide) g)

#print axioms exact_cyclic_K21
#print axioms exact_cyclic_deletion_K22
end Wild21
