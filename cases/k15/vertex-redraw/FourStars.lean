import VertexRedraw
namespace VertexRedraw
open EdgeWalk WildDeletion

def limits (c : C) := #[83924,26932,31598,2116,55060,17873,76810,73804,
  85743,64895,83531,25705,102706,65614,71670][c.val]!

theorem certified : (colors.all fun c => (pool c).all fun m => loss m ≤ limits c) = true ∧
    Teams.total colors limits = 867981 ∧ Teams.total draws Draw.weight = 1000007 ∧
    draws.length = 176 ∧ (draws.all fun g => decide (g.wild.length = 10 ∧
      g.wild.Nodup ∧ ∀ e ∈ g.wild, e.1 < e.2)) = true := by native_decide

/-- All matchings extending the four ordinary stars admit the same ten wild
edges for this completion. The remaining pairs may even overlap across colors. -/
theorem four_stars (f : C → V → V) (inv : ∀ c x, f c (f c x) = x)
    (ne : ∀ c x, f c x ≠ x) (agree : ∀ c x, known c x = true → f c x = partner c x) :
    ∃ w : E, w.length=10 ∧ w.Nodup ∧ (∀ e ∈ w, e.1 < e.2) ∧
      ∀ c, Connected (Adj (w ++ actualEdges (f c))) := by
  classical
  have repr := fun c => represented c (f c) (inv c) (ne c) (agree c)
  let m := fun c => Classical.choose (repr c)
  have spec (c) : m c ∈ pool c ∧ ∀ e ∈ m c, e ∈ actualEdges (f c) := Classical.choose_spec (repr c)
  let blocked := fun (g : Draw) (c : C) => !passes 0 (g.wild ++ m c)
  obtain ⟨checks,tot,weight,_,legal⟩ := certified
  obtain ⟨g,hg,wins⟩ := FiveColors.weighted_survivor draws colors Draw.weight blocked limits
    (fun c hc => by
      have bound := of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp checks c hc) _ (spec c).1)
      have flip (b : Bool) (n : Nat) : (if !b then n else 0) = (if b then 0 else n) := by cases b <;> rfl
      simpa only [blocked,flip,loss] using bound)
    (by omega)
  obtain ⟨len,uniq,order⟩ := of_decide_eq_true (List.all_eq_true.mp legal g hg)
  refine ⟨g.wild,len,uniq,order,?_⟩
  intro c
  have present : c ∈ colors := (by decide : ∀ k : C, k ∈ colors) c
  have path : passes 0 (g.wild ++ m c) = true := by simpa [blocked] using wins c present
  have step {e} (h : e ∈ g.wild ++ m c) : e ∈ g.wild ++ actualEdges (f c) :=
    List.mem_append.mpr ((List.mem_append.mp h).imp_right ((spec c).2 e))
  intro a b
  exact Walk.mapInto id (fun _ _ h => Walk.step (.stay _) (h.imp step step))
    (connected_of_passes 0 _ path a b)
#print axioms four_stars
end VertexRedraw
