import InfiniteEven
import Exact30

namespace WildSieve.EvenTriples
open WildExact

/-- The K30 counting theorem supplies the next order below the ordinary-kernel
family beginning at K36. -/
theorem exact_six_mul_from_five (m : Nat) (lo : 5≤m) :
    ∀ g : Coloring (6*m) (6*m-1),Exact g (4*m) := by
  by_cases first : m=5
  · subst m
    exact Thirty.Graph.exact_K30
  exact exact_six_mul m (by omega)

#print axioms exact_six_mul_from_five
end WildSieve.EvenTriples
