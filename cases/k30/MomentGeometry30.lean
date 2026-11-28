import MomentPairs30
import PatternGeometry

namespace WildSieve.Thirty.Graph
open Finset
local instance (priority := 2000) geometryVertexEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq
export SixCounts (two_from wedge_view wedge_size through_le event event_union event_empty event_pattern_union)

theorem event_mass {P : Pattern} (ok : Triples P) : (event P).card=ways (10-P.card) :=
  SixCounts.event_mass 10 (by decide) ok

end WildSieve.Thirty.Graph
