import TripleNeighbors30
import WedgeCount

namespace WildSieve.Thirty.Graph
open Finset
local instance (priority := 2000) wedgeCountEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq

noncomputable abbrev wedgesAt := @SixCounts.wedgesAt 30 29

theorem all_wedges_lower (F : Factor V C) :
    4060*1898≤(∑ A∈triples,(wedgesAt F A).card)+2640*defect F :=
  SixCounts.all_wedges_lower F 65 2457 1898 (degree_le F) (incidence_squares F) (by decide) (by decide)

end WildSieve.Thirty.Graph
