import ThreeCutRepair
import SixFamily

namespace WildExact.RootContraction
open Finset WildDeletion

/-- A counterexample one vertex below a settled even order must defeat every
cost-preserving contraction of every even optimum. -/
theorem barrier {n : Nat} (hn : 3≤n) (g : Coloring (n+1) n)
    (no : ¬Exact (restrict g) ((2*n+2)/3)) {w : Lines (n+1)} (win : Works g w)
    (size : w.card≤(2*n+2)/3) :
    (∃ a : Fin n,Touch w a.castSucc (Fin.last n)) ∧ ∀ a : Fin n,Touch w a.castSucc (Fin.last n) →
      3≤(sides g w a).card ∧ ¬∃ u v,∀ S∈sides g w a,WildCuts.Cross S u v := by
  classical
  have noUpper : ¬Upper (restrict g) w.card := by
    rintro ⟨w',leg,sz,works⟩
    exact no (exact_of_upper ⟨w',leg,sz.trans size,works⟩ (fun _ => odd_lower hn _))
  constructor
  · by_contra! h
    exact noUpper (untouched_upper g win ⟨0,by omega⟩ h)
  · intro a ha
    constructor
    · by_contra! small
      exact noUpper (two_sides_upper g win ha (by omega) (by omega))
    · rintro ⟨u,v,hit⟩
      exact noUpper ⟨_,repair_legal (legal a w) u v,(repair_size _ u v).trans (saves_edge ha),
        crossing_works g win a u v hit⟩

/-- Every coloring at K_(6m−1), m ≥ 5, either attains 4m or has a winning
even completion at the same cost and the obstruction described by barrier. -/
theorem six_predecessor (m n : Nat) (lo : 5≤m) (order : n+1=6*m) (g : Coloring n n) :
    let G := augment (n:=n) (by omega) g
    Exact g (4*m) ∨ ∃ w : Lines (n+1),Legal w ∧ w.card=4*m ∧ Works G w ∧
      (∃ a : Fin n,Touch w a.castSucc (Fin.last n)) ∧ ∀ a : Fin n,Touch w a.castSucc (Fin.last n) →
        3≤(sides G w a).card ∧ ¬∃ u v,∀ S∈sides G w a,WildCuts.Cross S u v := by
  classical
  dsimp only
  let G := augment (n:=n) (by omega) g
  by_cases exact : Exact g (4*m)
  · exact Or.inl exact
  · have even := WildSieve.EvenTriples.exact_six_mul_from_five m lo
    rw [←order,Nat.add_sub_cancel] at even
    obtain ⟨w,leg,card,win⟩ := (even G).1
    have cost : (2*n+2)/3=4*m := by omega
    have no : ¬Exact (restrict G) ((2*n+2)/3) := by simpa [G,cost] using exact
    have condition := barrier (by omega) G no win (by omega)
    exact Or.inr ⟨w,leg,card,win,condition⟩

#print axioms six_predecessor
end WildExact.RootContraction
