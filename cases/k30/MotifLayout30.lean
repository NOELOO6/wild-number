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
    test _ S=true := by
  classical
  let cut (e : Finset α) := e.subtype (·∈L)
  let G := S.image cut
  let back : ↥L ↪ α := Function.Embedding.subtype _
  have recover (e : Finset α) (he : e∈S) : (cut e).map back=e :=
    subtype_map_of_mem (sub e he)
  have original : mapped back G=S := by
    ext e
    constructor
    · intro h
      obtain ⟨u,hu,rfl⟩ := mem_map.mp h
      obtain ⟨e,he,rfl⟩ := mem_image.mp hu
      change (cut e).map back∈S
      rw [recover e he]
      exact he
    · intro h
      exact mem_map.mpr ⟨cut e,mem_image_of_mem _ h,recover _ h⟩
  let emb : ↥L ↪ Fin 10 := (Fintype.equivFin ↥L).toEmbedding.trans
    (Fin.castLEEmb (by simpa only [Fintype.card_coe] using order))
  let H := mapped emb G
  have size : H.card=S.card := by rw [show H=mapped emb G from rfl,mapped,card_map,←original,mapped,card_map]
  have edges (p) (hp : p∈H) : p.card=2 := by
    obtain ⟨q,hq,rfl⟩ := mem_map.mp hp
    obtain ⟨e,he,rfl⟩ := mem_image.mp hq
    change ((cut e).map emb).card=2
    rw [card_map,←card_map (f:=back),recover e he]
    exact sizes e he
  rw [←original,changeLabel _ _ back G,←changeLabel _ _ emb G]
  exact finite H size edges

theorem graph_on_blocks {α : Type} [DecidableEq α] (L : Finset α) (order : L.card≤10)
    (S : Finset (Finset α)) (sizes : ∀ e∈S,e.card=2) (sub : ∀ e∈S,e⊆L) : wins S=true := by
  apply reduce_to_ten L order S sizes sub (fun _ _ E => wins E) (fun _ _ _ _ f E => wins_mapped f E)
  intro H _ edges
  by_cases empty : H.card=0
  · exact decide_eq_true (Or.inl empty)
  · exact decide_eq_true (Or.inr (finite_graph H edges (Nat.pos_of_ne_zero empty)))

end WildSieve.Thirty.Motifs
