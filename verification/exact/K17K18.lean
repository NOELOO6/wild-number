import GlobalCount
namespace WildExact
open Seventeen Finset

theorem K17_upper (g : Coloring 17 17) : Upper g 12 := by
  classical
  have good : ∃ l,(failing (partners g) l).card=0 := by
    by_contra! none
    have count := many_wins g
    simp [wins,none] at count
  obtain ⟨l,hl⟩ := good
  apply winning_layout g l
  intro c bad
  have zero := Finset.card_eq_zero.mp hl
  have yes : c∈failing (partners g) l := Finset.mem_filter.mpr ⟨mem_univ _,(lost_spec _ _).mpr bad⟩
  rw [zero] at yes
  simp at yes

/-- Twelve distinct legal wild edges suffice for every minimum proper coloring
of K17 and K18, and every successful choice has at least twelve edges. -/
theorem K17_K18 : (∀ g : Coloring 17 17, Exact g 12) ∧ (∀ g : Coloring 18 17, Exact g 12) :=
  exact_pair (n:=17) (by decide) K17_upper

#print axioms Seventeen.many_wins
#print axioms K17_K18
end WildExact
