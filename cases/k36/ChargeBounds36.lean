import MomentGeometry36

namespace WildSieve.ThirtySix
open Finset
open scoped Classical
local instance (priority := 2000) chargeVertexEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq

private theorem detached_count (F : Factor V C) (P Q : Pattern) :
    ((family F).filter (Detached P Q)).card=10*(marks F (vertices (P∪Q))ᶜ).card := by
  classical
  rw [←pattern_card,pattern_filter]
  congr 1
  ext R; simp [Detached,Separate]

private theorem neighbor_wide {F : Factor V C} {P Q : Pattern} (p : P∈family F) (q : Q∈family F)
    (wide : Separate P Q) : ((family F).filter (Detached P Q)).card≤29000 := by
  have full := (pattern_mem.mp p).1.combine (pattern_mem.mp q).1 ((separate_iff _ _).mp wide)
  have d := blocks_disjoint (pattern_mem.mp p).1 ((separate_iff _ _).mp wide)
  have cnt := full.card_vertices
  rw [card_union_of_disjoint d,pattern_size p,pattern_size q] at cnt
  have sz : (vertices (P∪Q))ᶜ.card=24 := by rw [card_compl,Fintype.card_fin,cnt]
  rw [detached_count]
  exact Nat.mul_le_mul_left 10 ((marks_le_labeled _ _).trans (labels_le_24 _ _ sz))

private theorem neighbor_wedge {F : Factor V C} {P Q : Pattern} (p : P∈family F) (q : Q∈family F)
    (w : Wedge P Q) : ((family F).filter (Detached P Q)).card≤47580 := by
  have cnt := w.2.1.card_vertices
  rw [wedge_size p q w] at cnt
  have sz : (vertices (P∪Q))ᶜ.card=27 := by rw [card_compl,Fintype.card_fin,cnt]
  rw [detached_count]
  exact Nat.mul_le_mul_left 10 ((marks_le_labeled _ _).trans (labels_le_27 _ _ sz))

private theorem leaves {F : Factor V C} {P Q : Pattern} (p : P∈family F) (q : Q∈family F)
    (w : Wedge P Q) : ((family F).filter (JoinsLeaf P Q)).card≤80 ∧
      ((family F).filter (JoinsCenter P Q)).card≤80 := by
  classical
  obtain ⟨A,B,D,rfl,rfl,ab,ad,bd⟩ := wedge_view p q w
  have root := (pattern_mem.mp p).1
  have sa := root.size A (mem_insert_self _ _)
  have sb := root.size B (by simp)
  have difference : ({A,B} : Pattern) \ {A,D}={B} := by
    ext X
    by_cases xa : X=A <;> by_cases xb : X=B <;> by_cases xd : X=D <;> simp_all
  have intersection : ({A,B} : Pattern)∩{A,D}={A} := by
    ext X
    by_cases xa : X=A <;> by_cases xb : X=B <;> by_cases xd : X=D <;> simp_all
  have leaf : (family F).filter (JoinsLeaf {A,B} {A,D})=(family F).filter (fun R => B∈R) := by
    ext R; simp [JoinsLeaf,difference]
  have center : (family F).filter (JoinsCenter {A,B} {A,D})=(family F).filter (fun R => A∈R) := by
    ext R; simp [JoinsCenter,intersection]
  rw [leaf,center]
  exact ⟨through_le F B sb,through_le F A sa⟩

theorem charge_add (p : Prop) (a b : Nat) : charge p a+charge p b=charge p (a+b) := by
  by_cases h : p <;> simp [h]

private theorem bound_charge {S : Finset Pattern} (P : Prop) (test : Pattern → Prop)
    [DecidablePred test] (k n : Nat) (bound : P → (S.filter test).card≤k) :
    (∑ R∈S,charge (P ∧ test R) n)≤charge P (k*n) := by
  classical
  by_cases h : P
  · simp only [charge,h,true_and,ite_true,←sum_filter,sum_const,nsmul_eq_mul,Nat.cast_id]
    exact Nat.mul_le_mul_right _ (bound h)
  · simp [charge,h]

theorem symmetric_row {F : Factor V C} {P Q : Pattern} (p : P∈family F) (q : Q∈family F) :
    (∑ R∈family F,symmetricCost P Q R)≤charge (Separate P Q) (29000*ways 6)+
      charge (Wedge P Q) (80*ways 8+ways 9) := by
  classical
  have one := bound_charge (Separate P Q) (Detached P Q) 29000 (ways 6) (neighbor_wide p q)
  have two := bound_charge (Wedge P Q) (JoinsCenter P Q) 80 (ways 8) (fun h => (leaves p q h).2)
  have tri : ((family F).filter (ClosesTriangle P Q)).card≤1 := by
    apply card_le_one.mpr
    intro R h S k
    exact (mem_filter.mp h).2.trans (mem_filter.mp k).2.symm
  have three := bound_charge (Wedge P Q) (ClosesTriangle P Q) 1 (ways 9) (fun _ => tri)
  simpa only [symmetricCost,sum_add_distrib,one_mul,Nat.add_assoc,charge_add] using
    Nat.add_le_add (Nat.add_le_add one two) three

theorem oriented_row {F : Factor V C} {P Q : Pattern} (p : P∈family F) (q : Q∈family F) :
    (∑ R∈family F,orientedCost P Q R)≤charge (Wedge P Q) (47580*ways 7+80*ways 8) := by
  classical
  have one := bound_charge (Wedge P Q) (Detached P Q) 47580 (ways 7) (neighbor_wedge p q)
  have two := bound_charge (Wedge P Q) (JoinsLeaf P Q) 80 (ways 8) (fun h => (leaves p q h).1)
  simpa only [orientedCost,sum_add_distrib,charge_add] using Nat.add_le_add one two

end WildSieve.ThirtySix
