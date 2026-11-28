import PairPlacement
namespace WildAnchor
open Finset

/-- Distinct witnesses for the same outcome are disjoint, so their lower
counts add. -/
theorem lower_from_disjoint {X Y : Type} [Fintype Y] [DecidableEq Y] (T : Finset X)
    (f : X → Y → Prop) (lost : Y → Prop) [∀ x y,Decidable (f x y)] [DecidablePred lost]
    (w : X → Nat) (price : ∀ x,w x≤(univ.filter (f x)).card)
    (unique : ∀ x∈T,∀ z∈T,∀ y,f x y → f z y → x=z)
    (included : ∀ x∈T,∀ y,f x y → lost y) :
    (∑ x∈T,w x)≤(univ.filter lost).card := by
  let event (x : X) := univ.filter (f x)
  have dis : (T : Set X).PairwiseDisjoint event := by
    intro x hx z hz ne
    exact disjoint_left.mpr fun y hy h => ne (unique x hx z hz y (mem_filter.mp hy).2 (mem_filter.mp h).2)
  have sub : T.biUnion event ⊆ univ.filter lost := by
    intro y hy
    obtain ⟨x,hx,h⟩ := mem_biUnion.mp hy
    exact mem_filter.mpr ⟨mem_univ _,included x hx y (mem_filter.mp h).2⟩
  have b := card_le_card sub
  rw [card_biUnion dis] at b
  exact (sum_le_sum fun x _ => price x).trans b

theorem count_by_outcome {X Y : Type} [Fintype X] [Fintype Y] (f : X → Y → Prop)
    [∀ x y,Decidable (f x y)] :
    (∑ x,(univ.filter fun y => f x y).card)=∑ y,(univ.filter fun x => f x y).card := by
  calc
    _ = ∑ x, ∑ y, if f x y then (1 : Nat) else 0 := by simp only [sum_boole,Nat.cast_id]
    _ = ∑ y, ∑ x, if f x y then (1 : Nat) else 0 := sum_comm
    _ = _ := by simp only [sum_boole,Nat.cast_id]

theorem loss_upper {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq Y]
    (f : X → Y → Prop) [∀ x y,Decidable (f x y)] (lost : Y → Prop) [DecidablePred lost]
    (w : X → Nat) (cover : ∀ y,lost y → ∃ x,f x y)
    (cost : ∀ x,(univ.filter (f x)).card≤w x) :
    (univ.filter lost).card≤∑ x,w x := by
  let event (x : X) := univ.filter (f x)
  have sub : univ.filter lost ⊆ univ.biUnion event := by
    intro y hy
    obtain ⟨x,e⟩ := cover y (mem_filter.mp hy).2
    exact mem_biUnion.mpr ⟨x,mem_univ _,mem_filter.mpr ⟨mem_univ _,e⟩⟩
  exact (card_le_card sub).trans (card_biUnion_le.trans (sum_le_sum fun x _ => cost x))

theorem occupied_credit {Ω A : Type} [Fintype Ω] [DecidableEq Ω]
    (H : Ω → Finset A) (lost : Finset Ω) (credit : Ω → Nat)
    (mem : ∀ x,x∈lost ↔ (H x).Nonempty)
    (pointwise : ∀ x,(if (H x).Nonempty then 1 else 0)+credit x≤(H x).card) :
    lost.card+(∑ x,credit x)≤∑ x,(H x).card := by
  classical
  have total := sum_le_sum (s:=univ) (fun x _ => pointwise x)
  rw [sum_add_distrib] at total
  have cnt : (∑ x,if (H x).Nonempty then 1 else 0)=lost.card := by
    calc
      _ = ∑ x : Ω,if x∈lost then (1 : Nat) else 0 :=
        sum_congr rfl fun x _ => by simp only [mem]
      _ = _ := by simp
  rwa [cnt] at total
end WildAnchor
