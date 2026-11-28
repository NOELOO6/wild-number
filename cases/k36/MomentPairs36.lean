import Patterns36
import WedgeCount36
import PatternPairs

namespace WildSieve.ThirtySix
open Finset
local instance (priority := 2000) momentPairsEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq
abbrev Pattern := Blocks V
export SixCounts (family Separate Wedge wide touching separate_iff)

theorem wide_lower (F : Factor V C) :
    100*((marks F univ).card*8727)≤(wide F).card+100*(8875*defect F) := by
  rw [SixCounts.wide_tally,←Nat.mul_add]
  exact Nat.mul_le_mul_left _ (disjoint_count F)

theorem touching_lower (F : Factor V C) : 7140*3104≤(touching F).card+3240*defect F :=
  (all_wedges_lower F).trans (Nat.add_le_add_right (SixCounts.touching_tally F) _)

end WildSieve.ThirtySix
