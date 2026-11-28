import MotifFive30
import Mathlib.Data.Fintype.EquivFin

namespace WildSieve.Thirty.Motifs
open Finset WildSieve.EdgeDeletion

/-- Transfer a computation invariant under injective relabeling to the actual
triple blocks. The ambient vertex type can be arbitrarily large. -/
theorem reduce_to_ten {α : Type} [DecidableEq α] (L : Finset α) (order : L.card≤10)
    (S : Finset (Finset α)) (sizes : ∀ e∈S,e.card=2) (sub : ∀ e∈S,e⊆L)
    (test : (γ : Type) → [DecidableEq γ] → Finset (Finset γ) → Bool)
    (changeLabel : ∀ (γ δ : Type) [DecidableEq γ] [DecidableEq δ] (f : γ ↪ δ) (E : Finset (Finset γ)),
      test δ (mapped f E)=test γ E)
    (finite : ∀ H : Finset (Finset (Fin 10)), H.card=S.card → (∀ e∈H,e.card=2) → test _ H=true) :
    test _ S=true :=
  reduce_to_order L order S sizes sub test changeLabel finite

theorem graph_on_blocks {α : Type} [DecidableEq α] (L : Finset α) (order : L.card≤10)
    (S : Finset (Finset α)) (sizes : ∀ e∈S,e.card=2) (sub : ∀ e∈S,e⊆L) : wins S=true := by
  apply reduce_to_ten L order S sizes sub (fun _ _ E => wins E) (fun _ _ _ _ f E => wins_mapped f E)
  intro H _ edges
  by_cases empty : H.card=0
  · exact decide_eq_true (Or.inl empty)
  · exact decide_eq_true (Or.inr (finite_graph H edges (Nat.pos_of_ne_zero empty)))

end WildSieve.Thirty.Motifs
