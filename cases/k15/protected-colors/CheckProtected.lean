import Protected
import Teams
namespace Protected
set_option interpreter.prefer_native true

theorem exact_budgets : valid a = true ∧ valid b = true ∧ perms.size * 128 = 645120 ∧
    ca = #[66048,55552,83456,31104,74496,50304,79360,77440,67200,74240,74752] ∧
    cb = #[55296,61952,75264,61056,79872,65280,78272,86400,79296,82816,82048] ∧
    (rooted.all (· ≤ 80584960)) = true ∧
    (types.all (fun t => unrooted t ≤ 1196032)) = true ∧
    16*80584960 < 2*645120000 ∧ 17*1196032 < 2*10321920 := by native_decide

private theorem constants {X : Type} (xs : List X) (k : Nat) :
    Teams.total xs (fun _ => k) = xs.length*k := by
  induction xs with
  | nil => simp [Teams.total]
  | cons x xs ih => simp [Teams.total_cons, ih, Nat.add_mul, Nat.add_comm]

/-- The losses may be weighted and the budget may differ by color. -/
theorem low_penalty_budget {L C : Type} (layouts : List L) (cs : List C)
    (loss : L → C → Nat) (budget : C → Nat)
    (h : ∀ c ∈ cs, Teams.total layouts (fun l => loss l c) ≤ budget c)
    (room : Teams.total cs budget < 2*layouts.length) :
    ∃ l ∈ layouts, Teams.total cs (loss l) < 2 := by
  apply Classical.byContradiction
  intro no
  have low : ∀ l ∈ layouts, 2 ≤ Teams.total cs (loss l) := by
    intro l hl
    by_cases h : Teams.total cs (loss l) < 2
    · exact False.elim (no ⟨l,hl,h⟩)
    · omega
  have minTotal := Teams.total_mono layouts (fun _ => 2) (fun l => Teams.total cs (loss l)) low
  have upper := Teams.total_mono cs (fun c => Teams.total layouts (fun l => loss l c)) budget h
  rw [Teams.transpose, constants] at minTotal
  omega

/-- A protected color can appear twice in cs. Repeated draws implement
    the integer weights on the candidate layouts. -/
theorem low_penalty {L C : Type} (layouts : List L) (cs : List C) (loss : L → C → Nat)
    (cap : Nat) (h : ∀ c ∈ cs, Teams.total layouts (fun l => loss l c) ≤ cap)
    (room : cs.length * cap < 2*layouts.length) :
    ∃ l ∈ layouts, Teams.total cs (loss l) < 2 := by
  apply low_penalty_budget layouts cs loss (fun _ => cap) h
  rwa [constants]

#print axioms exact_budgets
#print axioms low_penalty_budget
end Protected
