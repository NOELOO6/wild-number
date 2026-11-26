import UniformCuts
import EdgeWalk
namespace WildCuts
open Finset WildDeletion EdgeWalk

/-- Two nontrivial cuts with a common point outside have an edge crossing both. -/
private theorem cross_pair {V : Type} {s t : Finset V} {r : V}
    (hs : s.Nonempty) (ht : t.Nonempty) (rs : r ∉ s) (rt : r ∉ t) :
    ∃ a b : V, a ∈ s ∧ b ∉ s ∧ ((a ∈ t ∧ b ∉ t) ∨ (b ∈ t ∧ a ∉ t)) := by
  classical
  by_cases common : ∃ x, x ∈ s ∧ x ∈ t
  · obtain ⟨x,xs,xt⟩ := common
    exact ⟨x,r,xs,rs,Or.inl ⟨xt,rt⟩⟩
  · obtain ⟨x,xs⟩ := hs
    obtain ⟨y,yt⟩ := ht
    exact ⟨x,y,xs,fun ys => common ⟨y,ys,yt⟩,Or.inr ⟨yt,fun xt => common ⟨x,xs,xt⟩⟩⟩

def Cross {V : Type} (s : Finset V) (a b : V) :=
  (a ∈ s ∧ b ∉ s) ∨ (b ∈ s ∧ a ∉ s)

theorem cross_all {V I : Type} [Nontrivial V] (r : V) (bad : Finset I) (side : I → Finset V)
    (small : bad.card < 3) (genuine : ∀ i ∈ bad, (side i).Nonempty ∧ r ∉ side i) :
    ∃ a b : V, a ≠ b ∧ ∀ i ∈ bad, Cross (side i) a b := by
  classical
  by_cases nonempty : bad.Nonempty
  · obtain ⟨i,hi⟩ := nonempty
    by_cases another : ∃ j ∈ bad, j ≠ i
    · obtain ⟨j,hj,ji⟩ := another
      obtain ⟨a,b,ha,hb,hjcross⟩ := cross_pair (genuine i hi).1 (genuine j hj).1
        (genuine i hi).2 (genuine j hj).2
      refine ⟨a,b,fun eq => hb (eq ▸ ha),?_⟩
      intro k hk
      by_cases ki : k = i
      · simpa [ki] using (Or.inl ⟨ha,hb⟩ : Cross (side i) a b)
      by_cases kj : k = j
      · simpa [kj] using hjcross
      have h := Finset.two_lt_card_iff.mpr ⟨k,i,j,hk,hi,hj,ki,kj,Ne.symm ji⟩
      omega
    · obtain ⟨a,ha⟩ := (genuine i hi).1
      have hr := (genuine i hi).2
      refine ⟨a,r,fun eq => hr (eq ▸ ha),?_⟩
      intro j hj
      have eq : j = i := not_not.mp (fun hn => another ⟨j,hj,hn⟩)
      exact eq ▸ Or.inl ⟨ha,hr⟩
  · obtain ⟨b,hb⟩ := exists_ne r
    exact ⟨r,b,Ne.symm hb,fun i hi => (nonempty ⟨i,hi⟩).elim⟩

private theorem reverseWalk {n : Nat} {w : List (Edge n)} {a b} (h : Walk (Adj w) a b) :
    Walk (Adj w) b a := by
  induction h with
  | stay => exact .stay _
  | step _ e ih => exact (Walk.step (E := Adj w) (.stay _) e.symm).join ih

/-- If every nontrivial closed side avoiding the root crosses the proposed
edge, that one edge gives genuine paths between all ordinary vertices. -/
theorem connected_by_crossing {n : Nat} (w m : List (Edge n)) (r a b : Fin n)
    (cuts : ∀ s : Finset (Fin n), s.Nonempty → r ∉ s →
      (∀ x y, Adj (w++m) x y → (x ∈ s ↔ y ∈ s)) → Cross s a b) :
    Connected (Adj (((a,b)::w)++m)) := by
  classical
  let E := Adj (((a,b)::w)++m)
  have reach (v : Fin n) : Walk E r v := by
    by_contra hv
    let s := univ.filter (fun x => ¬ Walk E r x)
    have mem (x : Fin n) : x ∈ s ↔ ¬ Walk E r x := by simp [s]
    have invariant (x y : Fin n) (e : E x y) : x ∈ s ↔ y ∈ s := by
      rw [mem,mem]
      exact not_congr ⟨fun h => .step h e,fun h => .step h e.symm⟩
    have old (x y : Fin n) (e : Adj (w++m) x y) : E x y := by
      rcases e with e | e
      · exact Or.inl (List.mem_cons_of_mem _ e)
      · exact Or.inr (List.mem_cons_of_mem _ e)
    have cross := cuts s ⟨v,(mem v).2 hv⟩ (fun hr => (mem r).1 hr (.stay r))
      (fun x y e => invariant x y (old x y e))
    have eq := invariant a b (Or.inl (by simp [E]))
    rcases cross with ⟨ha,hb⟩ | ⟨hb,ha⟩
    · exact hb (eq.mp ha)
    · exact ha (eq.mpr hb)
  exact fun x y => (reverseWalk (reach x)).join (reach y)
end WildCuts
