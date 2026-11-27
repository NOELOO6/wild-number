import Thirteen
import NineTrace
namespace WildExact

set_option maxHeartbeats 0
private theorem checked_budgets : K13.fastCheck=true := by native_decide
private theorem checked_paths : K13.pathCheck=true := by native_decide

/-- For every minimum proper coloring, nine legal wild edges suffice and
every set of legal wild edges connecting all colors has size at least nine. -/
theorem K13_K14 : (∀ g : Coloring 13 13, Exact g 9) ∧ (∀ g : Coloring 14 13, Exact g 9) :=
  exact_pair (n:=13) (by decide)
    (fun g => K13.build_upper g checked_budgets checked_paths Nine.nine_points)

#print axioms K13_K14
end WildExact
