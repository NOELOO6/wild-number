import Bounds

namespace WildCuts
open EdgeWalk
set_option maxHeartbeats 5000000
set_option maxRecDepth 50000

def groups21 : Blocks (Fin 21) (Fin 7) where
  tag x := ⟨x.val/3, by omega⟩
  rep i := ⟨3*i.val, by omega⟩
  section_ := by decide

theorem unrestricted_K21 (m : Fin 21 → List (Edge 21))
    (complete : ∀ x y, x ≠ y → ∃ c, Adj (m c) x y)
    (proper : ∀ c x y z, Adj (m c) x y → Adj (m c) x z → y = z) :
    Solution m 15 := by
  apply graph_bound (k := 10) (base := 14) groups21 0 _ complete proper (by decide)
  · decide +kernel
  · native_decide
  · decide

#print axioms unrestricted_K21
end WildCuts
