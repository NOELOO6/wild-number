import Delete
namespace CheckBase
open WildDeletion
abbrev V := Fin 15
def relations (r : V → V → Bool) (x y : V) : Prop := r x y = true

/-- Each vertex has a strictly shorter route to 0 through a valid neighbour.
    Both orientations are recorded so this also certifies directed reachability. -/
theorem by_parents (r : V → V → Bool) (depth : V → Nat) (parent : V → V)
    (h : ∀ v, v = 0 ∨ (r v (parent v) = true ∧ r (parent v) v = true ∧
          depth (parent v) < depth v)) : Connected (relations r) := by
  have all (v : V) : Walk (relations r) v 0 ∧ Walk (relations r) 0 v := by
    have aux (n : Nat) : ∀ x, depth x = n → Walk (relations r) x 0 ∧ Walk (relations r) 0 x := by
      induction n using Nat.strongRecOn with
      | ind n ih =>
        intro x hx
        rcases h x with h0 | ⟨forward, back, down⟩
        · subst x; exact ⟨.stay _, .stay _⟩
        · obtain ⟨a,b⟩ := ih (depth (parent x)) (hx ▸ down) (parent x) rfl
          exact ⟨(Walk.step (Walk.stay x) forward).join a, .step b back⟩
    exact aux (depth v) v rfl
  intro a b
  exact (all a).1.join (all b).2

theorem cut_blocks {V : Type} (r : V → V → Prop) (side : V → Bool)
    (a b : V) (ha : side a = true) (hb : side b = false)
    (closed : ∀ x y, r x y → side x = side y) : ¬Connected r := by
  intro h
  have eqside {u v : V} (w : Walk r u v) : side u = side v := by
    induction w with
    | stay => rfl
    | step _ e ih => exact ih.trans (closed _ _ e)
  have eq := eqside (h a b)
  simp [ha,hb] at eq
end CheckBase
