import KeepTwoCheck
import BoundaryProof

namespace CrossBoundary
open VertexRedraw EdgeWalk WildDeletion SixBoundary

private theorem branch (rs : List Row) (bs : List (List Row)) (used alive : Nat)
    (ch : Choices rs bs) (legal : compatible used rs) (ok : retain bs used alive=true) :
    enough 2 (remaining alive rs)=true := by
  induction ch generalizing used alive with
  | nil => exact ok
  | @cons r opts rs bs member _ ih =>
    have val := List.all_eq_true.mp ok r member
    exact ih _ _ legal.2 (by simpa [legal.1] using val)

theorem from_original (f : C→V→V)
    (inv : ∀ c x,f c (f c x)=x) (ne : ∀ c x,f c x≠x)
    (proper : ∀ c d,c≠d → ∀ x,f c x≠f d x)
    (agree : ∀ c x,fixedAt c x=true → f c x=ref c x) :
    ∃ is : List Nat,is.Nodup ∧ is.length=2 ∧ ∀ i∈is,∃ g,
      FixedSix.all[i]?=some g ∧ FixedSix.succeeds g=true ∧
      ∀ c,Connected (Adj (trial g++actualEdges (f c))) := by
  obtain ⟨is,nd,len,h⟩ := wins_of_choices 2 originalBits crossing possible order (by decide) (by decide)
    (fun rs choices legal => branch rs _ _ _ choices legal retained)
    f inv proper (represented f inv ne proper agree)
  refine ⟨is,nd,len,?_⟩
  intro i hi
  obtain ⟨yes,g,eq,win⟩ := h i hi
  exact ⟨g,eq,by simpa [originalBits,bit_lookup,eq] using yes,win⟩
#print axioms from_original
end CrossBoundary
