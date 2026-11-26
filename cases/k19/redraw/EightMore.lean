import EightBridge
import TableLink
import AllRoots

namespace WildMenu
open WildCuts EdgeWalk WildDeletion

/-- Any eight of the usual nineteen round-robin colors may be replaced together. -/
theorem eight_redrawn (g : WildLower.Coloring V) (changed : Finset V) (count : changed.card ≤ 8)
    (kept : ∀ c ∉ changed, ∀ i, Adj (g.edges c) (minusPoint c i) (plusPoint c i)) :
    ∃ w : List (Edge 19), w.Nodup ∧ (∀ e ∈ w, e.1 < e.2) ∧ w.length = 13 ∧
      ∀ c, Connected (Adj (w ++ g.edges c)) := by
  apply redraw_budget g changed kept 4274742 (eight_budget_from_search RawMenu.all_roots evaluated_losses)
  rw [total_weight]
  omega

#print axioms eight_redrawn
end WildMenu
