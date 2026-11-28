import CyclicNormal
import Cyclic25Check
import CyclicCutSound

namespace Wild25
open EdgeWalk WildExact WildDeletion

private theorem admits : ∀ t x y : V,(x=1 → y=t) → (∀ u : V,u*x=1 → t.val≤(u*y).val) →
    (∀ u : V,u*y=1 → t.val≤(u*x).val) → allowed t x y=true := by native_decide

private theorem layout_facts : layouts.all (fun bs =>
    (List.finRange 25).all (fun x => bs.flatten.contains x) &&
    (Rotation.CutTest.drawing bs).length==17 &&
    (Rotation.CutTest.drawing bs).all (fun e => e.1 != e.2)) = true := by native_decide

/-- Every minimum proper coloring admitting a 25-cycle on vertices that
permutes the colors attains the lower bound of seventeen. -/
theorem exact_cyclic_K25 (g : Coloring 25 25) (v : V ≃ V)
    (rot : Rotation.Cyclic g v) : Exact g 17 := by
  obtain ⟨w,cyc,t,minimum⟩ := Rotation.normalized_coordinates g v (by decide) (by decide) rot
  have valid (x y : V) (ne : x≠y) (col : g.paint (w x) (w y)=missingColor g (w 0)) : allowed t x y=true := by
    obtain ⟨one,a,b⟩ := minimum x y ne col
    exact admits t x y one a b
  obtain ⟨s,ok,edges⟩ := Rotation.find_allowed_starter g w (by decide) cyc (allowed t) acceptsStarter
    valid (List.all_eq_true.mp normalized_starters t (List.mem_finRange t))
  obtain ⟨T,hT,win⟩ := List.any_eq_true.mp ok
  obtain ⟨bs,hb,rfl⟩ := List.mem_map.mp hT
  obtain ⟨hc,ne⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp layout_facts bs hb)
  obtain ⟨haveAll,sz⟩ := Bool.and_eq_true_iff.mp hc
  apply exact_of_upper _ (fun _ => odd_lower (by decide) g)
  apply Rotation.upper_of_connected g (by decide) w cyc (List.finRange 25) id List.mem_finRange
    s (Rotation.CutTest.drawing bs) edges (beq_iff_eq.mp sz).le
    (fun e he => bne_iff_ne.mp (List.all_eq_true.mp ne e he)) _ ?_
  · intro z e he
    simpa [Rotation.shift] using he
  · intro c _
    exact Rotation.CutTest.connected bs
      (fun x => List.contains_iff_mem.mp (List.all_eq_true.mp haveAll x (List.mem_finRange x))) s win c

theorem exact_cyclic_deletion_K26 (g : Coloring 26 25) (v : V ≃ V)
    (rot : Rotation.Cyclic (restrict g) v) : Exact g 17 := by
  obtain ⟨⟨w,legal,sz,win⟩,_⟩ := exact_cyclic_K25 (restrict g) v rot
  exact exact_of_upper (upper_from_deletion g ⟨w,legal,sz.le,win⟩)
    (fun _ => even_lower (by decide) g)

#print axioms exact_cyclic_K25
#print axioms exact_cyclic_deletion_K26
end Wild25
