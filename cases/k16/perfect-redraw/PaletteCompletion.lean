import MatchingModel

namespace WildExact.PaletteCompletion
open Finset
variable {n k : Nat}

/-- Equality of the specified color classes on ordinary edges; diagonal entries are ignored. -/
def Retains (g h : Coloring n k) (P : Finset (Fin k)) :=
  ∀ c,c∉P → ∀ x y,x≠y → (g.paint x y=c ↔ h.paint x y=c)

private theorem missing_iff (g : Coloring n n) (x c : Fin n) :
    missingColor g x=c ↔ Absent g x c := by
  constructor
  · intro e
    exact e ▸ absent_missing g x
  · intro h
    exact ((unique_missing g x).choose_spec.2 c h).symm

theorem completion_iff (odd : n%2=1) (g h : Coloring n n) (P : Finset (Fin n)) :
    Retains (augment odd g) (augment odd h) P ↔ Retains g h P := by
  constructor
  · intro keep c hc x y ne
    simpa using keep c hc x.castSucc y.castSucc (fun e => ne (Fin.castSucc_inj.mp e))
  · intro keep c hc
    have root (x : Fin n) : missingColor g x=c ↔ missingColor h x=c := by
      rw [missing_iff,missing_iff]
      exact ⟨fun a y ne col => a y ne ((keep c hc x y ne).mpr col),
        fun a y ne col => a y ne ((keep c hc x y ne).mp col)⟩
    intro x y ne
    cases x using Fin.lastCases <;> cases y using Fin.lastCases
    case last.last => exact (ne rfl).elim
    case last.cast y => simpa [augment] using root y
    case cast.last x => simpa [augment] using root x
    case cast.cast x y => simpa using keep c hc x y (fun e => ne (congrArg Fin.castSucc e))

/-- An arbitrary proper ordinary redraw of a deletion lifts to an even redraw of the
original coloring, including any reassignment of its missing colors. -/
theorem lift_redraw (odd : n%2=1) (base : Coloring (n+1) n) (h : Coloring n n)
    (P : Finset (Fin n)) (keep : Retains (restrict base) h P) :
    ∃ H : Coloring (n+1) n, restrict H=h ∧ Retains base H P := by
  refine ⟨augment odd h,restrict_augment odd h,?_⟩
  have yes := (completion_iff odd (restrict base) h P).mpr keep
  intro c hc x y ne
  simpa only [augment_restrict_edge odd base x y ne] using yes c hc x y ne

#print axioms lift_redraw
end WildExact.PaletteCompletion
