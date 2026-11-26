import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Perm

/- A uniform bound on the number of ways to carry a prescribed side of a
cut onto another one. The proof restricts each permutation to both sides. -/
namespace WildCuts
open Finset
variable {V : Type} [Fintype V] [DecidableEq V]

theorem fiber_bound (s t : Finset V) :
    (univ.filter (fun p : Equiv.Perm V => s.map p.toEmbedding = t)).card ≤
      if s.card = t.card then s.card.factorial * (Fintype.card V - s.card).factorial else 0 := by
  classical
  by_cases eq : s.card = t.card
  · rw [if_pos eq, ← Fintype.card_subtype]
    let Left := {x : V // x ∈ s}
    let Right := {x : V // x ∈ t}
    let Outside := {x : V // x ∉ s}
    let Other := {x : V // x ∉ t}
    have mem {p : Equiv.Perm V} (h : s.map p.toEmbedding = t) (v : V) : v ∈ s ↔ p v ∈ t := by
      rw [← h, Finset.mem_map_equiv]; simp
    let restrict := fun p : {p : Equiv.Perm V // s.map p.toEmbedding = t} =>
      ((p.1.subtypeEquiv (mem p.2) : Left ≃ Right),
       (p.1.subtypeEquiv (fun x => not_congr (mem p.2 x)) : Outside ≃ Other))
    have inj : Function.Injective restrict := by
      intro a b hab
      apply Subtype.ext
      ext v
      by_cases hv : v ∈ s
      · exact congrArg (fun z : (Left ≃ Right) × (Outside ≃ Other) => (z.1 ⟨v,hv⟩ : V)) hab
      · exact congrArg (fun z : (Left ≃ Right) × (Outside ≃ Other) => (z.2 ⟨v,hv⟩ : V)) hab
    have hL : Fintype.card Left = s.card := Fintype.card_coe _
    have hR : Fintype.card Right = t.card := Fintype.card_coe _
    have hO : Fintype.card Outside = Fintype.card V - s.card := by
      simpa only [← hL] using Fintype.card_subtype_compl (fun x => x ∈ s)
    have hT : Fintype.card Other = Fintype.card V - t.card := by
      simpa only [← hR] using Fintype.card_subtype_compl (fun x => x ∈ t)
    have hi := Fintype.card_le_of_injective restrict inj
    rwa [Fintype.card_prod, Fintype.card_equiv (Fintype.equivOfCardEq (hL.trans (eq.trans hR.symm))),
      Fintype.card_equiv (Fintype.equivOfCardEq (hO.trans (by rw [eq,hT]))),hL,hO] at hi
  · rw [if_neg eq]
    have h : (univ.filter (fun p : Equiv.Perm V => s.map p.toEmbedding = t)) = ∅ := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro p hp
      have e := (Finset.mem_filter.mp hp).2
      exact eq (by rw [← e, Finset.card_map])
    simp [h]

/-- Count cuts using arbitrary layouts, arbitrary colors and arbitrary
candidate closed sides. Each hit is one equality of two actual vertex sets. -/
theorem choose_layout {I : Type} [Fintype I] (s t : I → Finset V) (k : Nat)
    (budget : (∑ i, if (s i).card = (t i).card then
       (s i).card.factorial * (Fintype.card V - (s i).card).factorial else 0) <
       (Fintype.card V).factorial * k) :
    ∃ p : Equiv.Perm V, (univ.filter (fun i => (s i).map p.toEmbedding = t i)).card < k := by
  classical
  have each (i : I) : (∑ p : Equiv.Perm V, if (s i).map p.toEmbedding = t i then 1 else 0) ≤
      (if (s i).card = (t i).card then (s i).card.factorial * (Fintype.card V - (s i).card).factorial else 0) := by
    rw [Finset.sum_boole, Nat.cast_id]
    exact fiber_bound (s i) (t i)
  have low : (∑ p : Equiv.Perm V, ∑ i : I, if (s i).map p.toEmbedding = t i then 1 else 0) <
      ∑ _p : Equiv.Perm V, k := by
    rw [Finset.sum_comm]
    calc
      _ ≤ _ := Finset.sum_le_sum (fun i _ => each i)
      _ < _ := budget
      _ = _ := by simp [Fintype.card_perm]
  obtain ⟨p,_,hp⟩ := Finset.exists_lt_of_sum_lt low
  exact ⟨p,by simpa only [Finset.sum_boole, Nat.cast_id] using hp⟩
end WildCuts
