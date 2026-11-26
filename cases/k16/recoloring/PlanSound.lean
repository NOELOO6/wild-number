import Recolor
namespace SixColors
open EdgeWalk WildDeletion
set_option interpreter.prefer_native true
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem solve_plan (p : Plan) (cert : rowOK p = true) (actual : List Item)
    (allowed : ∀ m ∈ actual, m ∈ pool p.root p.mask)
    (disjoint : ∀ a ∈ actual, ∀ m ∈ actual, compatible a m = true)
    (covers : ∀ i, (pool p.root p.mask).any (fun m => m.key.testBit i) = true →
      ∃ a ∈ actual, a.key.testBit i = true) :
    ∃ w : Edges, w.length = 10 ∧ (∀ m ∈ originals p.root, Connected (Adj (w++m))) ∧
      ∀ m ∈ actual, Connected (Adj (w++m.edges)) := by
  have finish (ms : List Item) (i : Nat) (h : works p ms i = true) (sub : ∀ m ∈ actual, m ∈ ms) :
      ∃ w : Edges, w.length = 10 ∧ (∀ m ∈ originals p.root, Connected (Adj (w++m))) ∧
        ∀ m ∈ actual, Connected (Adj (w++m.edges)) := by
    obtain ⟨base,rest⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨len,old⟩ := Bool.and_eq_true_iff.mp base
    exact ⟨_,beq_iff_eq.mp len, fun m hm => connected_of_passes 0 _ (List.all_eq_true.mp old m hm),
      fun m hm => connected_of_passes 0 _ (List.all_eq_true.mp rest m (sub m hm))⟩
  unfold rowOK at cert
  split at cert
  · exact finish _ _ cert allowed
  · obtain ⟨front,checks⟩ := Bool.and_eq_true_iff.mp cert
    obtain ⟨nonempty,lens⟩ := Bool.and_eq_true_iff.mp front
    let ms := pool p.root p.mask
    have anyPivot : ms.any (fun m => m.key.testBit (p.pivot-1)) = true := by
      have ne : (active p ms).isEmpty = false := by simpa using nonempty
      obtain ⟨m,hm⟩ := List.isEmpty_eq_false_iff_exists_mem.mp ne
      exact List.any_eq_true.mpr ⟨m,List.mem_filter.mp hm⟩
    obtain ⟨a,ha,hp⟩ := covers _ anyPivot
    have hmem : a ∈ active p ms := List.mem_filter.mpr ⟨allowed a ha, hp⟩
    have len : (active p ms).length = p.ids.length := beq_iff_eq.mp lens
    rw [← List.map_fst_zip (l₂ := p.ids) (Nat.le_of_eq len)] at hmem
    obtain ⟨⟨a',i⟩,hi,e⟩ := List.mem_map.mp hmem
    change a' = a at e
    subst a'
    exact finish _ i (List.all_eq_true.mp checks (a,i) hi)
      (fun m hm => List.mem_filter.mpr ⟨allowed m hm,disjoint a ha m hm⟩)


end SixColors
