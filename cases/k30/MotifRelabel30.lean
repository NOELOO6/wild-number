import MotifCheck30
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace WildSieve.Thirty.Motifs
open Finset WildSieve.EdgeDeletion
variable {α β : Type} [DecidableEq α] [DecidableEq β]

def mapped (f : α ↪ β) (S : Finset (Finset α)) := S.map (mapEmbedding f).toEmbedding

theorem nodes_mapped (f : α ↪ β) (S : Finset (Finset α)) : nodes (mapped f S)=(nodes S).map f := by
  ext y
  constructor
  · intro h
    obtain ⟨q,hq,hy⟩ := mem_biUnion.mp h
    obtain ⟨e,he,rfl⟩ := mem_map.mp hq
    obtain ⟨x,hx,rfl⟩ := mem_map.mp (show y∈e.map f from hy)
    exact mem_map.mpr ⟨x,mem_biUnion.mpr ⟨e,he,hx⟩,rfl⟩
  · intro h
    obtain ⟨x,hx,rfl⟩ := mem_map.mp h
    obtain ⟨e,he,xe⟩ := mem_biUnion.mp hx
    exact mem_biUnion.mpr ⟨e.map f,mem_map.mpr ⟨e,he,rfl⟩,mem_map.mpr ⟨x,xe,rfl⟩⟩

theorem center_mapped (f : α ↪ β) (S : Finset (Finset α)) : center (mapped f S)=center S := by
  unfold center
  rw [nodes_mapped]
  rw [decide_eq_decide]
  constructor
  · rintro ⟨y,hy,all⟩
    obtain ⟨x,hx,rfl⟩ := mem_map.mp hy
    refine ⟨x,hx,fun e he => ?_⟩
    have img := all (e.map f) (mem_map.mpr ⟨e,he,rfl⟩)
    exact mem_map' f |>.mp img
  · rintro ⟨x,hx,all⟩
    refine ⟨f x,mem_map.mpr ⟨x,hx,rfl⟩,?_⟩
    intro q hq
    obtain ⟨e,he,rfl⟩ := mem_map.mp hq
    exact mem_map.mpr ⟨x,all e he,rfl⟩

theorem pair_mapped (f : α ↪ β) (S : Finset (Finset α)) : pairCost (mapped f S)=pairCost S := by
  simp only [pairCost,nodes_mapped,card_map]

theorem credit_mapped (f : α ↪ β) (S : Finset (Finset α)) :
    tripleCredit (mapped f S)=tripleCredit S := by
  simp only [tripleCredit,nodes_mapped,card_map,center_mapped]

omit [DecidableEq α] [DecidableEq β] in
theorem map_bill (f : α ↪ β) (S : Finset (Finset α)) (k : Nat)
    (v : Finset (Finset α) → Nat) (w : Finset (Finset β) → Nat)
    (agree : ∀ T,w (mapped f T)=v T) :
    bill w k (mapped f S)=bill v k S := by
  simp only [bill,mapped,powersetCard_map,sum_map,RelEmbedding.coe_toEmbedding,mapEmbedding_apply]
  apply sum_congr rfl
  intro T _
  exact agree T

theorem wins_mapped (f : α ↪ β) (S : Finset (Finset α)) : wins (mapped f S)=wins S := by
  have hq := map_bill f S 2 pairCost pairCost (fun T => pair_mapped f T)
  have hb := map_bill f S 3 tripleCredit tripleCredit (fun T => credit_mapped f T)
  unfold wins
  rw [hq,hb]
  simp only [mapped,card_map]

/-- Transfer a computation invariant under injective relabeling to the actual
triple blocks. The ambient vertex type can be arbitrarily large. -/
theorem reduce_to_order {m : Nat} {α : Type} [DecidableEq α] (L : Finset α) (order : L.card≤m)
    (S : Finset (Finset α)) (sizes : ∀ e∈S,e.card=2) (sub : ∀ e∈S,e⊆L)
    (test : (γ : Type) → [DecidableEq γ] → Finset (Finset γ) → Bool)
    (changeLabel : ∀ (γ δ : Type) [DecidableEq γ] [DecidableEq δ] (f : γ ↪ δ) (E : Finset (Finset γ)),
      test δ (mapped f E)=test γ E)
    (finite : ∀ H : Finset (Finset (Fin m)), H.card=S.card → (∀ e∈H,e.card=2) → test _ H=true) :
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
  let emb : ↥L ↪ Fin m := (Fintype.equivFin ↥L).toEmbedding.trans
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

end WildSieve.Thirty.Motifs
