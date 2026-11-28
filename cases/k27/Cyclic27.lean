import CyclicNormal
import CyclicCutSound
import Cyclic27Check
namespace Wild27
open WildExact WildDeletion EdgeWalk
set_option maxRecDepth 30000

private theorem admits : ∀ t x y : V,(x=1 → y=t) → (∀ u : V,u*x=1 → t.val≤(u*y).val) →
    (∀ u : V,u*y=1 → t.val≤(u*x).val) → allowed t x y=true := by native_decide

private theorem facts : layouts.all (fun w =>
    (List.finRange 27).all (fun x => w.groups.flatten.contains x) &&
    (Rotation.CutTest.drawing w.groups).length==18 &&
    (Rotation.CutTest.drawing w.groups).all (fun e => e.1 != e.2) &&
    (List.finRange 27).all (fun z => (reps w).contains (rep w z) &&
      (Rotation.shift (Rotation.CutTest.drawing w.groups) (z-rep w z)).all
        (fun e => (Rotation.CutTest.drawing w.groups).contains e)))=true := by native_decide

/-- A cyclic minimum coloring of K27 has wild number eighteen. -/
theorem exact_cyclic_K27 (g : Coloring 27 27) (v : V ≃ V) (rot : Rotation.Cyclic g v) :
    Exact g 18 := by
  obtain ⟨w,cyc,t,minimum⟩ := Rotation.normalized_coordinates g v (by decide) (by decide) rot
  have valid (x y : V) (ne : x≠y) (col : g.paint (w x) (w y)=missingColor g (w 0)) : allowed t x y=true := by
    obtain ⟨one,a,b⟩ := minimum x y ne col
    exact admits t x y one a b
  obtain ⟨s,ok,edges⟩ := Rotation.find_allowed_starter g w (by decide) cyc (allowed t) acceptsStarter
    valid (List.all_eq_true.mp normalized_starters t (List.mem_finRange t))
  obtain ⟨T,hT,win⟩ := List.any_eq_true.mp ok
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hT
  obtain ⟨p1,period⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp facts q hq)
  obtain ⟨p2,ne⟩ := Bool.and_eq_true_iff.mp p1
  obtain ⟨cover,sz⟩ := Bool.and_eq_true_iff.mp p2
  have translated (z : V) := Bool.and_eq_true_iff.mp (List.all_eq_true.mp period z (List.mem_finRange z))
  apply exact_of_upper _ (fun _ => odd_lower (by decide) g)
  apply Rotation.upper_of_connected g (by decide) w cyc (reps q) (rep q)
    (fun z => List.contains_iff_mem.mp (translated z).1) s _ edges (beq_iff_eq.mp sz).le
    (fun e he => bne_iff_ne.mp (List.all_eq_true.mp ne e he))
    (fun z e he => List.contains_iff_mem.mp (List.all_eq_true.mp (translated z).2 e he))
  intro c hc
  exact Rotation.CutTest.connected_row q.groups
    (fun x => List.contains_iff_mem.mp (List.all_eq_true.mp cover x (List.mem_finRange x))) s c
    (beq_iff_eq.mp (List.all_eq_true.mp win _ (List.mem_map.mpr ⟨c,hc,rfl⟩)))

theorem exact_cyclic_deletion_K28 (g : Coloring 28 27) (v : V ≃ V)
    (rot : Rotation.Cyclic (restrict g) v) : Exact g 18 := by
  obtain ⟨⟨w,legal,sz,win⟩,_⟩ := exact_cyclic_K27 (restrict g) v rot
  exact exact_of_upper (upper_from_deletion g ⟨w,legal,sz.le,win⟩)
    (fun _ => even_lower (by decide) g)

#print axioms exact_cyclic_K27
#print axioms exact_cyclic_deletion_K28
end Wild27
