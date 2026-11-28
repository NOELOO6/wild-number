import MotifLayout30

namespace WildSieve.Thirty.Motifs
open Finset WildSieve.EdgeDeletion
variable {α β : Type} [DecidableEq α] [DecidableEq β]

/-- The third edge can be detached, or it can extend the first leaf or the
center of a wedge by one new block. -/
def coupon (p q r : Finset α) : Nat :=
  (if Disjoint p q ∧ Disjoint (p∪q) r then 1 else 0) +
  (if ¬Disjoint p q ∧ Disjoint (p∪q) r then 3 else 0) +
  (if ¬Disjoint p q ∧ ¬r⊆p∪q ∧ ¬Disjoint (p \ q) r then 2 else 0) +
  (if ¬Disjoint p q ∧ ¬r⊆p∪q ∧ ¬Disjoint (p∩q) r then 1 else 0)

def orderedThree {τ : Type} [DecidableEq τ] (T : Finset τ) (f : τ → τ → τ → Nat) :=
  ∑ p∈T,∑ q∈T.erase p,∑ r∈(T.erase p).erase q,f p q r

def costCheck (T : Finset (Finset α)) : Bool :=
  decide (T.card≠3 ∨ 2*tripleCredit T≤orderedThree T coupon)

private theorem local_check : sweep costCheck deck ∅ 3=true := by native_decide

theorem coupon_map (f : α ↪ β) (p q r : Finset α) :
    coupon (p.map f) (q.map f) (r.map f)=coupon p q r := by
  have diff : p.map f \ q.map f=(p \ q).map f := by
    ext y
    constructor
    · intro h
      obtain ⟨x,hx,rfl⟩ := mem_map.mp (mem_sdiff.mp h).1
      exact mem_map.mpr ⟨x,mem_sdiff.mpr ⟨hx,fun u => (mem_sdiff.mp h).2 ((mem_map' f).mpr u)⟩,rfl⟩
    · intro h
      obtain ⟨x,hx,rfl⟩ := mem_map.mp h
      exact mem_sdiff.mpr ⟨(mem_map' f).mpr (mem_sdiff.mp hx).1,fun u => (mem_sdiff.mp hx).2 ((mem_map' f).mp u)⟩
  simp only [coupon,←map_union,diff,←map_inter,map_subset_map,disjoint_map]

private theorem ordered_map {γ δ : Type} [DecidableEq γ] [DecidableEq δ]
    (e : γ ↪ δ) (T : Finset γ) (g : δ → δ → δ → Nat) :
    orderedThree (T.map e) g=orderedThree T (fun p q r => g (e p) (e q) (e r)) := by
  simp only [orderedThree,sum_map,←map_erase]

private theorem check_map (f : α ↪ β) (T : Finset (Finset α)) :
    costCheck (mapped f T)=costCheck T := by
  have ord : orderedThree (mapped f T) coupon=orderedThree T coupon := by
    rw [mapped,ordered_map]
    simp only [RelEmbedding.coe_toEmbedding,mapEmbedding_apply,coupon_map]
  unfold costCheck
  rw [credit_mapped,ord]
  simp only [mapped,card_map]

theorem three_covered {L : Finset α} (sz : L.card≤10) (T : Finset (Finset α))
    (sizes : ∀ e∈T,e.card=2) (sub : ∀ e∈T,e⊆L) (three : T.card=3) :
    2*tripleCredit T≤orderedThree T coupon := by
  have yes := reduce_to_ten L sz T sizes sub (fun _ _ E => costCheck E)
    (fun _ _ _ _ f E => check_map f E) (fun H hcard edges => by
      by_cases small : H.card=3
      · have legal : H⊆deck.toFinset := fun e he => List.mem_toFinset.mpr (mem_deck (edges e he))
        simpa only [empty_union] using sweep_sound costCheck deck ∅ H 3 legal small.le local_check
      · exact decide_eq_true (Or.inl small))
  exact (of_decide_eq_true yes).resolve_left (not_not.mpr three)

end WildSieve.Thirty.Motifs
