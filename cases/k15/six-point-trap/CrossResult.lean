import CrossCheck
import BoundaryProof
namespace CrossBoundary
open VertexRedraw EdgeWalk WildDeletion
/-- Every proper redraw of the 54 crossing edges has nineteen distinct
groupings, each of which connects all fifteen colors with ten wild edges. -/
theorem nineteen (f : C → V → V) (inv : ∀ c x, f c (f c x)=x)
    (ne : ∀ c x, f c x≠x) (proper : ∀ c d, c≠d → ∀ x, f c x≠f d x)
    (agree : ∀ c x, fixedAt c x=true → f c x=SixBoundary.ref c x) :
    ∃ is : List Nat, is.Nodup ∧ is.length=19 ∧ ∀ i∈is,
      ∃ g, FixedSix.all[i]?=some g ∧ ∀ c, Connected (Adj (trial g++actualEdges (f c))) := by
  have checked : (SixBoundary.scan pools 0 SixBoundary.initial).belowNineteen = 0 := by rw [census]
  exact SixBoundary.nineteen_of_options crossing possible order (by decide) (by decide)
    checked f inv proper
    (represented f inv ne proper agree)
#print axioms nineteen
end CrossBoundary
