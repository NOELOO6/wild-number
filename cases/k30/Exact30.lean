import GraphRows30

namespace WildSieve.Thirty.Graph
open Finset
local instance (priority := 2000) exactThirtyEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq

/-- For every one-factorization, the chance of avoiding all marked six-sets
when sampling a uniformly labeled twelve-cut obeys the certified bound. -/
theorem long_chance (F : Factor V C) : noHitChance F≤longPrice+(defect F : ℚ)/18000 := by
  have h := functional_certificate (graphEval F) (eval_zero F) (eval_linear F)
    (eval_dominates F) (graph_rows F)
  rw [eval_objective] at h
  linarith

theorem winning_partitions_K30 (F : Factor V C) :
    2211739995828567≤((shortBad F∪lateBad F)ᶜ).card :=
  winning_count_of_long F (long_of_noHitChance F (long_chance F))

/-- Every proper minimum edge coloring of the complete graph on thirty vertices
has wild number twenty. -/
theorem exact_K30 (g : WildExact.Coloring 30 29) : WildExact.Exact g 20 :=
  exact_of_noHitChance g (long_chance (coloringFactor g))

#print axioms winning_partitions_K30
#print axioms exact_K30
end WildSieve.Thirty.Graph
