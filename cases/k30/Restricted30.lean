import MomentPairs30
import RestrictedNeighbors

namespace WildSieve.Thirty.Graph
open Finset
local instance (priority := 2000) restrictedEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq

theorem neighbors_in_21 (F : Factor V C) (A U : Finset V) (a : A.card=3) (u : U.card=21) :
    ((neighbors F A).filter (fun B => B⊆U)).card≤51 := by
  simpa only [u] using SixCounts.restricted_neighbors F A U a

end WildSieve.Thirty.Graph
