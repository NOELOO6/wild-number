import SixCounts30
import TripleNeighbors

namespace WildSieve.Thirty.Graph
open Finset
local instance (priority := 2000) tripleNeighborsEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq
abbrev triples := SixCounts.triples 30
theorem triple_mem {A : Finset V} : A∈triples ↔ A.card=3 := SixCounts.triple_mem
theorem num_triples : triples.card=4060 := SixCounts.num_triples
noncomputable abbrev colorNeighbors := @SixCounts.colorNeighbors 30 29
noncomputable abbrev neighbors := @SixCounts.neighbors 30 29
theorem neigh_mem {F : Factor V C} {A B : Finset V} : B∈neighbors F A ↔
    B⊆Aᶜ ∧ B.card=3 ∧ ∃ c,Closed (F.f c) (A∪B) := SixCounts.neigh_mem
abbrev degree_le := @SixCounts.degree_le 30 29
noncomputable abbrev incidence := @SixCounts.incidence 30 29
abbrev incidence_squares := @SixCounts.incidence_squares 30 29 (by decide)

end WildSieve.Thirty.Graph
