import BoundaryOptions

namespace CrossBoundary
open VertexRedraw EdgeWalk WildDeletion
open SixBoundary (ref)

/-- Only ordinary edges with exactly one marked endpoint can change. -/
def locked (x y : V) : Bool :=
  x.val == 15 || y.val == 15 || (decide (x.val < 6) == decide (y.val < 6))
abbrev fixedAt := BoundaryOptions.fixedAt locked
abbrev possible := BoundaryOptions.possible locked
def crossing : R := points.flatMap fun x => points.filterMap fun y =>
  if x.val < 6 ∧ 6 ≤ y.val ∧ y.val < 15 then some (x,y) else none
def order : List C := [1,4,8,9,2,3,5,6,13,14,10,0,7,11,12]
def pools := order.map fun c => (possible c).map (SixBoundary.encodeWith crossing)

theorem represented (f : C → V → V) (inv : ∀ c x, f c (f c x) = x)
    (ne : ∀ c x, f c x ≠ x) (proper : ∀ c d, c≠d → ∀ x, f c x ≠ f d x)
    (agree : ∀ c x, fixedAt c x = true → f c x = ref c x) (c : C) :
    ∃ m ∈ possible c, respects (f c) m :=
  BoundaryOptions.represented locked (by native_decide) f inv ne proper agree c
end CrossBoundary
