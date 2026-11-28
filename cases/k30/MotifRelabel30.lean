import MotifCheck30
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

end WildSieve.Thirty.Motifs
