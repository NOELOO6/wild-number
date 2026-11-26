import OutsidePatterns
namespace SixBoundary
/-- Check every choice of starters and of three disjoint outside boxes.
For any possible pattern all fifteen colors must have a box. -/
theorem no_boxes : starters.length=455 ∧ (starters.filter possibleBox).isEmpty=true := by native_decide
#print axioms no_boxes
end SixBoundary
