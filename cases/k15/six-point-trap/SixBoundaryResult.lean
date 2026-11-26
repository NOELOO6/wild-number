import BoundaryProof
import SixBoundaryCounts
namespace SixBoundary
open VertexRedraw EdgeWalk WildDeletion

theorem valid_groupings : FixedSix.all.Nodup ∧
    (FixedSix.all.all (fun g => decide ((trial g).length=10 ∧ (trial g).Nodup)))=true := by native_decide

/-- Any proper completion agreeing at the six marked points admits at least
nineteen different indexed groupings. Each connects all fifteen old colors. -/
theorem nineteen_for_every_completion (f : C→V→V) (inv : ∀ c x,f c (f c x)=x)
    (ne : ∀ c x,f c x≠x) (proper : ∀ c d,c≠d → ∀ x,f c x≠f d x)
    (agree : ∀ c x,x.val<6 → f c x=ref c x) :
    ∃ is : List Nat,is.Nodup ∧ is.length=19 ∧ ∀ i∈is,
      ∃ g, FixedSix.all[i]?=some g ∧ (trial g).length=10 ∧ (trial g).Nodup ∧
        ∀ c,Connected (Adj (trial g++actualEdges (f c))) := by
  obtain ⟨is,nd,size,win⟩ := nineteen_of_census (by rw [all_completions]) f inv ne proper agree
  refine ⟨is,nd,size,?_⟩
  intro i hi
  obtain ⟨g,lookup,paths⟩ := win i hi
  have mem := List.mem_of_getElem? lookup
  have legal := of_decide_eq_true (List.all_eq_true.mp valid_groupings.2 g mem)
  exact ⟨g,lookup,legal.1,legal.2,paths⟩
#print axioms nineteen_for_every_completion
end SixBoundary
