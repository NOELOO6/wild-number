import ExactTrimmed
import ExactSplit
import ExactJoint

namespace WildSieve
open WildExact

private theorem exact_pair_interval (n : Nat) (lo : 77≤n) (hi : n≤153) (odd : n%2=1) :
    (∀ g : Coloring n n, Exact g ((2*n+2)/3)) ∧
    (∀ g : Coloring (n+1) n, Exact g ((2*n+2)/3)) := by
  by_cases medium : 83≤n
  · exact exact_medium n medium hi odd
  rcases (show n=77 ∨ n=79 ∨ n=81 by omega) with rfl|rfl|rfl
  · exact exact_K77_K78
  · exact exact_K79_K80
  · exact exact_K81_K82

/-- The conjectured formula for every minimum proper coloring at every
order from 77 through 154, inclusive. -/
theorem exact_77_to_154 (n : Nat) (lo : 77≤n) (hi : n≤154) :
    ∀ g : Coloring n (if n%2=1 then n else n-1), Exact g (4*((n+1)/2)/3) := by
  by_cases odd : n%2=1
  · rw [if_pos odd,show 4*((n+1)/2)/3=(2*n+2)/3 by omega]
    exact (exact_pair_interval n lo (by omega) odd).1
  rw [if_neg odd]
  cases n with
  | zero => omega
  | succ k =>
    rw [show 4*((k+1+1)/2)/3=(2*k+2)/3 by omega]
    exact (exact_pair_interval k (by omega) (by omega) (by omega)).2

#print axioms exact_77_to_154
end WildSieve
