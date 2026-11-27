import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
import TwoGroups

namespace WildExact.Regroup
open Finset WildDeletion

/-- Two ways of pairing the same finite set admit a common choice of one
point from each pair. The distinguished point can be put on the outside. -/
theorem paired_bisection {B I J : Type} [Fintype I] [Fintype J]
    (e : I × Bool ≃ B) (d : J × Bool ≃ B) (root : B) :
    ∃ side : B → Bool, side root = false ∧
      (∀ i, side (e (i,false)) ≠ side (e (i,true))) ∧
      (∀ j, side (d (j,false)) ≠ side (d (j,true))) := by
  classical
  let p := e.trans d.symm
  let nbr (i : I) := (univ : Finset Bool).image (fun b => (p (i,b)).1)
  have hall (S : Finset I) : S.card ≤ (S.biUnion nbr).card := by
    have inc : (S ×ˢ (univ : Finset Bool)).card ≤
        (S.biUnion nbr ×ˢ (univ : Finset Bool)).card := by
      apply card_le_card_of_injOn p _ p.injective.injOn
      rintro ⟨i,b⟩ h
      refine mem_product.mpr ⟨mem_biUnion.mpr ⟨i,(mem_product.mp h).1,?_⟩,mem_univ _⟩
      exact mem_image.mpr ⟨b,mem_univ _,rfl⟩
    simp only [card_product,card_univ,Fintype.card_bool] at inc
    omega
  obtain ⟨f,inj,edges⟩ := (all_card_le_biUnion_card_iff_existsInjective' nbr).mp hall
  have counts := Fintype.card_congr p
  simp only [Fintype.card_prod,Fintype.card_bool] at counts
  have onto := ((Fintype.bijective_iff_injective_and_card f).mpr ⟨inj,by omega⟩).2
  have pick (i : I) : ∃ b : Bool,(p (i,b)).1 = f i := by
    obtain ⟨b,_,h⟩ := mem_image.mp (edges i)
    exact ⟨b,h⟩
  choose bit hbit using pick
  let chosen (x : B) : Prop := ∃ i, e (i,bit i) = x
  have uniqueRight {j : J} {a b : Bool} (ha : chosen (d (j,a)))
      (hb : chosen (d (j,b))) : a=b := by
    obtain ⟨i,hi⟩ := ha
    obtain ⟨k,hk⟩ := hb
    have xi : p (i,bit i) = (j,a) := by simp [p,hi]
    have xk : p (k,bit k) = (j,b) := by simp [p,hk]
    have eq : i=k := inj <| (hbit i).symm.trans ((congrArg Prod.fst xi).trans
      ((congrArg Prod.fst xk).symm.trans (hbit k)))
    subst k
    exact congrArg Prod.snd (xi.symm.trans xk)
  have right (j : J) : ∃ a : Bool, chosen (d (j,a)) := by
    obtain ⟨i,hi⟩ := onto j
    let a := (p (i,bit i)).2
    have eq : p (i,bit i) = (j,a) := Prod.ext ((hbit i).trans hi) rfl
    exact ⟨a,i,by simpa [p] using congrArg d eq⟩
  let mark (x : B) := decide (chosen x)
  have leftDiff (i : I) : mark (e (i,false)) ≠ mark (e (i,true)) := by
    have key (b : Bool) : chosen (e (i,b)) ↔ bit i=b := by
      constructor
      · rintro ⟨k,hk⟩
        have eq := e.injective hk
        have ik := congrArg Prod.fst eq
        change k=i at ik
        subst k
        exact congrArg Prod.snd eq
      · rintro rfl
        exact ⟨i,rfl⟩
    simp only [mark,key]
    cases bit i <;> decide
  have rightDiff (j : J) : mark (d (j,false)) ≠ mark (d (j,true)) := by
    obtain ⟨a,ha⟩ := right j
    cases a
    · have hb : ¬ chosen (d (j,true)) := fun h => Bool.false_ne_true (uniqueRight ha h)
      simp [mark,ha,hb]
    · have hb : ¬ chosen (d (j,false)) := fun h => Bool.false_ne_true (uniqueRight h ha)
      simp [mark,ha,hb]
  by_cases r : mark root = false
  · exact ⟨mark,r,leftDiff,rightDiff⟩
  · exact ⟨fun x => !(mark x),by simpa using r,fun i => by simpa using leftDiff i,
      fun j => by simpa using rightDiff j⟩

section Fibers
variable {B A : Type} [Fintype B] [DecidableEq A]
variable (q : B → A)

abbrev HalfIndex := (a : A) × Fin (Fintype.card {x // q x = a} / 2)

private noncomputable def fiberPairs (even : ∀ a, Fintype.card {x // q x = a} % 2 = 0)
    (a : A) : Fin (Fintype.card {x // q x = a} / 2) × Bool ≃ {x // q x = a} :=
  Fintype.equivOfCardEq (by
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
    have := even a
    omega)

private noncomputable def pairs (even : ∀ a, Fintype.card {x // q x = a} % 2 = 0) :
    HalfIndex q × Bool ≃ B :=
  ((Equiv.sigmaProdDistrib _ _).trans (Equiv.sigmaCongrRight (fiberPairs q even))).trans
    (Equiv.sigmaFiberEquiv q)

private theorem class_pairs (even) (i : HalfIndex q) (b : Bool) :
    q (pairs q even (i,b)) = i.1 :=
  (fiberPairs q even i.1 (i.2,b)).property
end Fibers

/-- A side balances a class map if every class has equally many points
on the two sides. Both sides then meet the class of each point. -/
structure Balanced {B A : Type} (q : B → A) (side : B → Bool) : Prop where
  exchange : ∃ t : B ≃ B, ∀ x, q (t x) = q x ∧ side (t x) = !(side x)

private theorem balanced_of_pairs {A B I : Type} (q : B → A) (side : B → Bool)
    (e : I × Bool ≃ B) (same : ∀ i, q (e (i,false)) = q (e (i,true)))
    (diff : ∀ i, side (e (i,false)) ≠ side (e (i,true))) : Balanced q side := by
  let swap : I × Bool ≃ I × Bool := Equiv.prodCongr (Equiv.refl I) (⟨Bool.not,Bool.not,Bool.not_not,Bool.not_not⟩ : Bool ≃ Bool)
  let t := (e.symm.trans swap).trans e
  refine ⟨t,?_⟩
  intro x
  obtain ⟨⟨i,b⟩,rfl⟩ := e.surjective x
  change q (e (swap (e.symm (e (i,b))))) = _ ∧ side (e (swap (e.symm (e (i,b))))) = _
  rw [e.symm_apply_apply]
  change q (e (i,!b)) = _ ∧ side (e (i,!b)) = _
  have h := diff i
  cases b
  · exact ⟨(same i).symm,by simp only [Bool.not_false,Bool.not_true]; revert h; cases side (e (i,false)) <;> cases side (e (i,true)) <;> decide⟩
  · exact ⟨same i,by simp only [Bool.not_false,Bool.not_true]; revert h; cases side (e (i,false)) <;> cases side (e (i,true)) <;> decide⟩

theorem common_bisection {B A C : Type} [Fintype B] [Fintype A] [Fintype C]
    [DecidableEq A] [DecidableEq C] (q : B → A) (r : B → C) (root : B)
    (eq : ∀ a, Fintype.card {x // q x = a} % 2 = 0)
    (er : ∀ c, Fintype.card {x // r x = c} % 2 = 0) :
    ∃ side : B → Bool, side root = false ∧ Balanced q side ∧ Balanced r side := by
  obtain ⟨side,hroot,hq,hr⟩ := paired_bisection (pairs q eq) (pairs r er) root
  exact ⟨side,hroot,
    balanced_of_pairs q side _ (fun i => (class_pairs q eq i false).trans (class_pairs q eq i true).symm) hq,
    balanced_of_pairs r side _ (fun i => (class_pairs r er i false).trans (class_pairs r er i true).symm) hr⟩

theorem Balanced.hits {B A : Type} {q : B → A} {side : B → Bool}
    (h : Balanced q side) (x : B) : ∃ y, q y = q x ∧ side y = true := by
  obtain ⟨t,ht⟩ := h.exchange
  cases hx : side x
  · exact ⟨t x,(ht x).1,by simp [(ht x).2,hx]⟩
  · exact ⟨x,rfl,hx⟩

theorem Balanced.count {B A : Type} [Fintype B] {q : B → A} {side : B → Bool}
    (h : Balanced q side) : 2 * (univ.filter (fun x => side x = true)).card = Fintype.card B := by
  classical
  obtain ⟨t,ht⟩ := h.exchange
  have eq : (univ.filter (fun x => side x = true)).card =
      (univ.filter (fun x => ¬side x = true)).card := by
    apply card_bij (fun x _ => t x)
    · intro x hx
      have yes := (mem_filter.mp hx).2
      simp [(ht x).2,yes]
    · intro a _ b _ hab
      exact t.injective hab
    · intro b hb
      refine ⟨t.symm b, ?_, t.apply_symm_apply b⟩
      have key := (ht (t.symm b)).2
      rw [t.apply_symm_apply] at key
      have no := (mem_filter.mp hb).2
      cases hy : side (t.symm b) <;> simp_all
  have sum := filter_card_add_filter_neg_card_eq_card (s := (univ : Finset B)) (fun x => side x = true)
  rw [card_univ] at sum
  omega

#print axioms common_bisection

end WildExact.Regroup
