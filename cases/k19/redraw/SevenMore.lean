import MenuTable
namespace WildMenu
open WildCuts EdgeWalk WildDeletion Finset
set_option maxHeartbeats 4000000
set_option maxRecDepth 500000

def cap : Nat → Nat
  | 3 => 214281
  | 4 => 10716
  | 6 => 14106
  | 7 => 3723
  | 9 => 3996
  | _ => 0

def circle (c : V) := permutation (fun x =>
  if x.val = 18 then c else if x.val%2 = 0 then vertex (c.val+x.val/2+1)
    else vertex (c.val+19-(x.val/2+1)))

def plusPoint (c : V) (i : Fin 9) := vertex (c.val+i.val+1)
def minusPoint (c : V) (i : Fin 9) := vertex (c.val+19-(i.val+1))
theorem circle_edges : ∀ (c x : V), x ≠ (pairs 19).rep ((pairs 19).tag x) →
    ∃ i : Fin 9, circle c x = minusPoint c i ∧ circle c ((pairs 19).rep ((pairs 19).tag x)) = plusPoint c i := by
  decide +kernel

/-- This finite check is over actual vertex subsets and their weights in the
entire menu of layouts. It requires no hypothesis about the extra colors. -/
theorem cut_caps : ∀ s : Finset V, value hist (mask s) ≤ cap s.card := by native_decide
theorem circle_cost : ∀ c : V, charge (circle c) = 0 := by native_decide
theorem total_weight : weight = 34197948 := by native_decide
theorem one_extra (q : Equiv.Perm V) : charge q ≤ 4315437 := by
  unfold charge
  calc
    _ ≤ ∑ j : Finset (Fin 10), cap ((closedSides q j).card) :=
      Finset.sum_le_sum (fun j _ => cut_caps (closedSides q j))
    _ = ∑ j : Finset (Fin 10), cap ((side (pairs 19) j).card) := by simp [closedSides]
    _ ≤ 4315437 := by decide +kernel

/-- Given a menu budget, realize its clean layout as thirteen distinct real
lines and obtain actual vertex-to-vertex paths for every color. -/
theorem draw_thirteen (g : WildLower.Coloring V) (q : V → Equiv.Perm V)
    (edges : ∀ c x, x ≠ (pairs 19).rep ((pairs 19).tag x) →
      Adj (g.edges c) (q c x) (q c ((pairs 19).rep ((pairs 19).tag x))))
    (budget : (∑ c, charge (q c)) < weight) :
    ∃ w : List (Edge 19), w.Nodup ∧ (∀ e ∈ w, e.1 < e.2) ∧ w.length = 13 ∧
      ∀ c, Connected (Adj (w ++ g.edges c)) := by
  obtain ⟨r,_,avoid⟩ := find_clean q budget
  let es := wild groups19 r.place
  have paths (c : V) : Connected (Adj (es++g.edges c)) := by
    apply survivor r.place (q c) _ (edges c)
    intro i j h
    exact avoid c i j (congrArg Prod.snd h)
  have legal := tidy_properties es (wild_simple groups19 r.place)
  have stars : es.length = 13 := by
    unfold es wild
    rw [List.length_map]
    decide
  have allPaths c := tidy_connected es (g.edges c) (paths c)
  have lower := WildLower.thirteen_necessary g (tidy es) (fun e he => (legal.2.2 e he).ne) allPaths
  exact ⟨tidy es,legal.2.1,legal.2.2,by have := legal.1; omega,allPaths⟩

theorem redraw_budget (g : WildLower.Coloring V) (changed : Finset V)
    (circleKept : ∀ c ∉ changed, ∀ i, Adj (g.edges c) (minusPoint c i) (plusPoint c i))
    (limit : Nat) (one : ∀ q, charge q ≤ limit) (afford : changed.card*limit < weight) :
    ∃ w : List (Edge 19), w.Nodup ∧ (∀ e ∈ w, e.1 < e.2) ∧ w.length = 13 ∧
      ∀ c, Connected (Adj (w ++ g.edges c)) := by
  classical
  obtain ⟨any,hany⟩ := Classical.axiomOfChoice (coordinates (k:=9) (by decide) (by decide +kernel)
    g.edges g.complete g.proper)
  let q := fun c => if c ∈ changed then any c else circle c
  apply draw_thirteen g q
  · intro c x hx
    by_cases h : c ∈ changed
    · simpa [q,h] using hany c x hx
    · obtain ⟨i,ha,hb⟩ := circle_edges c x hx
      simpa [q,h,ha,hb] using circleKept c h i
  · calc
      _ ≤ ∑ c : V, if c ∈ changed then limit else 0 := by
        apply Finset.sum_le_sum
        intro c _
        by_cases h : c ∈ changed
        · simpa [q,h] using one (any c)
        · simp [q,h,circle_cost]
      _ = changed.card*limit := by simp
      _ < _ := afford

theorem seven_redrawn (g : WildLower.Coloring V) (changed : Finset V) (count : changed.card ≤ 7)
    (kept : ∀ c ∉ changed, ∀ i, Adj (g.edges c) (minusPoint c i) (plusPoint c i)) :
    ∃ w : List (Edge 19), w.Nodup ∧ (∀ e ∈ w, e.1 < e.2) ∧ w.length = 13 ∧
      ∀ c, Connected (Adj (w ++ g.edges c)) := by
  apply redraw_budget g changed kept 4315437 one_extra
  rw [total_weight]; omega
#print axioms seven_redrawn
end WildMenu
