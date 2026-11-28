import TripleNeighbors36
import WedgeCount

namespace WildSieve.ThirtySix
open Finset
local instance (priority := 2000) wedgeCountEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq

noncomputable abbrev wedgesAt := @SixCounts.wedgesAt 36 35

theorem all_wedges_lower (F : Factor V C) :
    7140*3104≤(∑ A∈triples,(wedgesAt F A).card)+3240*defect F :=
  SixCounts.all_wedges_lower F 80 3456 3104 (degree_le F) (incidence_squares F) (by decide) (by decide)

end WildSieve.ThirtySix
