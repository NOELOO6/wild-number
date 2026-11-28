import ExactInterval
import ExactLarge

namespace WildSieve
open WildExact

/-- The exact wild number for every minimum proper coloring of Kₙ, for
every n ≥ 77, including all odd and even orders. -/
theorem exact_from_77 (n : Nat) (lo : 77≤n) :
    ∀ g : Coloring n (if n%2=1 then n else n-1),Exact g (4*((n+1)/2)/3) := by
  by_cases early : n≤154
  · exact exact_77_to_154 n lo early
  · exact exact_from_155 n (by omega)

#print axioms exact_from_77
end WildSieve
