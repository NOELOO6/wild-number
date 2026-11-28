import Starters21
import CyclicExtraction

namespace Wild21
open WildExact

abbrev Cyclic := @Rotation.Cyclic 20

theorem find_starter (g : Coloring 21 21) (v : V ≃ V) (rot : Cyclic g v)
    (test : Edges → Bool) (checked : scan test 10 points.tail [] []=true) :
    ∃ s, test s=true ∧ ∀ e∈s, e.1≠e.2 ∧ g.paint (v e.1) (v e.2)=missingColor g (v 0) :=
  Rotation.find_starter (by decide) g v rot test checked

end Wild21
