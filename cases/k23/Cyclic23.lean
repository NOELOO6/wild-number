import Cyclic23Check
import CyclicCutSound

namespace Wild23
open EdgeWalk WildExact WildDeletion

private theorem layout_facts : layouts.all (fun bs =>
    (List.finRange 23).all (fun x => bs.flatten.contains x) &&
    (Rotation.CutTest.drawing bs).length==16 &&
    (Rotation.CutTest.drawing bs).all (fun e => e.1 != e.2)) = true := by native_decide

/-- Every minimum proper coloring admitting a 23-cycle on vertices that
permutes the colors attains the lower bound of sixteen. -/
theorem exact_cyclic_K23 (g : Coloring 23 23) (v : V ≃ V)
    (rot : Rotation.Cyclic g v) : Exact g 16 := by
  obtain ⟨s,ok,edges⟩ := Rotation.find_starter (by decide : 23%2=1) g v rot
    acceptsStarter every_starter_passes
  obtain ⟨T,hT,win⟩ := List.any_eq_true.mp ok
  obtain ⟨bs,hb,rfl⟩ := List.mem_map.mp hT
  obtain ⟨hc,ne⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp layout_facts bs hb)
  obtain ⟨haveAll,sz⟩ := Bool.and_eq_true_iff.mp hc
  apply exact_of_upper _ (fun _ => odd_lower (by decide) g)
  apply Rotation.upper_of_connected g (by decide) v rot (List.finRange 23) id List.mem_finRange
    s (Rotation.CutTest.drawing bs) edges (beq_iff_eq.mp sz).le
    (fun e he => bne_iff_ne.mp (List.all_eq_true.mp ne e he)) _ ?_
  · intro z e he
    simpa [Rotation.shift] using he
  · intro c _
    exact Rotation.CutTest.connected bs
      (fun x => List.contains_iff_mem.mp (List.all_eq_true.mp haveAll x (List.mem_finRange x))) s win c

theorem exact_cyclic_deletion_K24 (g : Coloring 24 23) (v : V ≃ V)
    (rot : Rotation.Cyclic (restrict g) v) : Exact g 16 := by
  obtain ⟨⟨w,legal,sz,win⟩,_⟩ := exact_cyclic_K23 (restrict g) v rot
  exact exact_of_upper (upper_from_deletion g ⟨w,legal,sz.le,win⟩)
    (fun _ => even_lower (by decide) g)

#print axioms exact_cyclic_K23
#print axioms exact_cyclic_deletion_K24
end Wild23
