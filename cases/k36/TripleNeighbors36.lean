import Multiplicity36
import TripleNeighbors

namespace WildSieve.ThirtySix
open Finset
local instance (priority := 2000) tripleNeighborsEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq
abbrev triples := SixCounts.triples 36
theorem triple_mem {A : Finset V} : A∈triples ↔ A.card=3 := SixCounts.triple_mem
theorem num_triples : triples.card=7140 := SixCounts.num_triples
noncomputable abbrev colorNeighbors := @SixCounts.colorNeighbors 36 35
noncomputable abbrev neighbors := @SixCounts.neighbors 36 35
theorem neigh_mem {F : Factor V C} {A B : Finset V} : B∈neighbors F A ↔
    B⊆Aᶜ ∧ B.card=3 ∧ ∃ c,Closed (F.f c) (A∪B) := SixCounts.neigh_mem
abbrev degree_le := @SixCounts.degree_le 36 35
noncomputable abbrev incidence := @SixCounts.incidence 36 35
abbrev incidence_squares := @SixCounts.incidence_squares 36 35 (by decide)

end WildSieve.ThirtySix
