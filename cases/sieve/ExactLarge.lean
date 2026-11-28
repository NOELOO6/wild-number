import GeometricLarge
import GeometricRange

namespace WildSieve
open WildExact

private theorem odd_large_pair (n : Nat) (lo : 155≤n) (odd : n%2=1) :
    (∀ g : Coloring n n,Exact g ((2*n+2)/3)) ∧ (∀ g : Coloring (n+1) n,Exact g ((2*n+2)/3)) := by
  by_cases small : n≤1205
  · exact Geometric.medium n lo small odd
  · exact Geometric.large n (by omega) odd

/-- All minimum proper colorings at every order from 155 upward satisfy
the predicted formula. -/
theorem exact_from_155 (n : Nat) (lo : 155≤n) :
    ∀ g : Coloring n (if n%2=1 then n else n-1),Exact g (4*((n+1)/2)/3) := by
  by_cases odd : n%2=1
  · rw [if_pos odd,show 4*((n+1)/2)/3=(2*n+2)/3 by omega]
    exact (odd_large_pair n lo odd).1
  rw [if_neg odd]
  cases n with
  | zero => omega
  | succ k =>
    rw [show 4*((k+1+1)/2)/3=(2*k+2)/3 by omega]
    exact (odd_large_pair k (by omega) (by omega)).2

#print axioms exact_from_155
end WildSieve
