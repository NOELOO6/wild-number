import MomentGeometry30
import Restricted30
import OrderedMotifs30

namespace WildSieve.Thirty.Graph
open Finset Motifs
local instance (priority := 2000) rowEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq

private noncomputable def attached (F : Factor V C) (U A : Finset V) : Finset Pattern :=
  ((neighbors F A).filter (·⊆U)).image (fun Z => {A,Z})

private theorem attached_cap (F : Factor V C) (U A : Finset V) (u : U.card=21) (a : A.card=3) :
    (attached F U A).card≤51 := card_image_le.trans (neighbors_in_21 F A U a u)

private theorem detached_in {F : Factor V C} {P Q R : Pattern} (r : R∈family F)
    (ok : Triples (P∪Q∪R)) (apart : Disjoint (P∪Q) R) :
    R∈patterns F (vertices (P∪Q))ᶜ := by
  rw [pattern_filter]
  refine mem_filter.mpr ⟨r,?_⟩
  have d := supports_disjoint ok apart
  exact fun _ h => mem_compl.mpr (fun e => disjoint_left.mp d e h)

private theorem attached_in {F : Factor V C} {P Q R : Pattern} {A : Finset V}
    (r : R∈family F) (ok : Triples (P∪Q∪R)) (inc : A∈P∪Q) (ar : A∈R)
    (new : ¬R⊆P∪Q) : R∈attached F (vertices (P∪Q))ᶜ A ∧ (P∪Q∪R).card=(P∪Q).card+1 := by
  obtain ⟨Z,az,eq⟩ := two_from (pattern_size r) ar
  have fresh : Z∉P∪Q := fun h => new (eq ▸ insert_subset inc (singleton_subset_iff.mpr h))
  have outside : Z⊆(vertices (P∪Q))ᶜ := by
    intro x hx
    apply mem_compl.mpr
    intro covered
    obtain ⟨B,hB,xb⟩ := mem_biUnion.mp covered
    have zmem : Z∈R := eq ▸ mem_insert_of_mem (mem_singleton_self _)
    have same := ok.only (mem_union_left _ hB) (mem_union_right _ zmem) xb hx
    exact fresh (same ▸ hB)
  have united : P∪Q∪R=insert Z (P∪Q) := by
    have one : (P∪Q)∪{Z}=insert Z (P∪Q) := by ext x; simp only [mem_union,mem_singleton,mem_insert]; tauto
    rw [eq,union_insert,one,insert_comm,insert_eq_of_mem inc]
  refine ⟨mem_image.mpr ⟨Z,mem_filter.mpr ⟨other_neighbor az (eq ▸ r),outside⟩,eq.symm⟩,?_⟩
  rw [united,card_insert_of_not_mem fresh]

private theorem row_sum {α : Type} [DecidableEq α] (H S : Finset α) (k : Nat) :
    (∑ R∈H,if R∈S then k else 0)≤S.card*k := by
  rw [←sum_filter,sum_const,nsmul_eq_mul,Nat.cast_id]
  exact Nat.mul_le_mul_right _ (card_le_card (fun _ h => (mem_filter.mp h).2))

private theorem separate_row {F : Factor V C} {P Q : Pattern} (p : P∈family F) (q : Q∈family F)
    (ss : Separate P Q) :
    (∑ R∈family F,coupon P Q R*(event (P∪Q∪R)).card)≤9420*ways 4 := by
  classical
  let U := (vertices (P∪Q))ᶜ
  have d := (separate_iff _ _).mp ss
  have bd := blocks_disjoint (pattern_mem.mp p).1 d
  have sz : (P∪Q).card=4 := by rw [card_union_of_disjoint bd,pattern_size p,pattern_size q]
  have both := (pattern_mem.mp p).1.combine (pattern_mem.mp q).1 d
  have us : U.card=18 := by
    have v := both.card_vertices
    rw [sz] at v
    change (vertices (P∪Q))ᶜ.card=18
    rw [card_compl,Fintype.card_fin,v]
  have each (R : Pattern) (r : R∈family F) : coupon P Q R*(event (P∪Q∪R)).card ≤
      if R∈patterns F U then ways 4 else 0 := by
    by_cases ok : Triples (P∪Q∪R)
    swap
    · rw [event_empty ok,mul_zero]; exact Nat.zero_le _
    by_cases apart : Disjoint (P∪Q) R
    · have fit := detached_in r ok apart
      rw [if_pos (show R∈patterns F U from fit),event_mass ok,card_union_of_disjoint apart,sz,pattern_size r]
      simp [coupon,bd,apart]
    · simp [coupon,bd,apart]
  have cap := (marks_le_labeled F U).trans (labels_le_18 F U us)
  have upper : (patterns F U).card≤9420 := by rw [pattern_card]; omega
  exact ((sum_le_sum each).trans (row_sum _ _ _)).trans (Nat.mul_le_mul_right _ upper)

private theorem single_or_empty {P Q : Pattern}
    (pq : P≠Q) (no : ¬Separate P Q) (nw : ¬Wedge P Q) :
    ∀ R, (event (P∪Q∪R)).card=0 := by
  intro R
  apply event_empty
  intro ok
  have valid := ok.sub (subset_union_left : P∪Q⊆P∪Q∪R)
  by_cases d : Disjoint P Q
  · exact no ((separate_iff _ _).mpr (supports_disjoint valid d))
  · exact nw ⟨pq,valid,d⟩

private theorem wedge_row {F : Factor V C} {P Q : Pattern}
    (p : P∈family F) (q : Q∈family F) (w : Wedge P Q) :
    (∑ R∈family F,coupon P Q R*(event (P∪Q∪R)).card)≤44400*ways 5+153*ways 6 := by
  classical
  let U := (vertices (P∪Q))ᶜ
  obtain ⟨A,B,D,pe,qe,ab,ad,bd⟩ := wedge_view p q w
  have sz := wedge_size p q w
  have us : U.card=21 := by
    have v := w.2.1.card_vertices
    rw [sz] at v
    change (vertices (P∪Q))ᶜ.card=21
    rw [card_compl,Fintype.card_fin,v]
  have meet : P∩Q={A} := by
    rw [pe,qe]; ext X
    by_cases x : X=A <;> by_cases y : X=B <;> by_cases z : X=D <;> simp_all
  have leaf : P \ Q={B} := by
    rw [pe,qe]; ext X
    by_cases x : X=A <;> by_cases y : X=B <;> by_cases z : X=D <;> simp_all
  have ap : A∈P := pe ▸ mem_insert_self _ _
  have bp : B∈P := pe ▸ mem_insert_of_mem (mem_singleton_self _)
  have a := (pattern_mem.mp p).1.size A ap
  have b := (pattern_mem.mp p).1.size B bp
  let H := family F
  have each (R : Pattern) (r : R∈H) : coupon P Q R*(event (P∪Q∪R)).card ≤
      (if R∈patterns F U then 3*ways 5 else 0) +
      (if R∈attached F U B then 2*ways 6 else 0) +
      (if R∈attached F U A then ways 6 else 0) := by
    by_cases ok : Triples (P∪Q∪R)
    swap
    · rw [event_empty ok,mul_zero]; exact Nat.zero_le _
    have first : (if Disjoint (P∪Q) R then 3 else 0)*(event (P∪Q∪R)).card ≤
        if R∈patterns F U then 3*ways 5 else 0 := by
      split_ifs with d h h
      · rw [event_mass ok,card_union_of_disjoint d,sz,pattern_size r]
      · exact False.elim (h (detached_in r ok d))
      all_goals simp
    have next (Z : Finset V) (inc : Z∈P) (c : Nat) :
        (if ¬R⊆P∪Q ∧ Z∈R then c else 0)*(event (P∪Q∪R)).card ≤
        if R∈attached F U Z then c*ways 6 else 0 := by
      split_ifs with h fit fit
      · obtain ⟨_,total⟩ := attached_in r ok (mem_union_left _ inc) h.2 h.1
        rw [event_mass ok,total,sz]
      · exact False.elim (fit (attached_in r ok (mem_union_left _ inc) h.2 h.1).1)
      all_goals simp
    have n := add_le_add (add_le_add first (next B bp 2)) (next A ap 1)
    simpa only [coupon,w.2.2,not_false_eq_true,false_and,true_and,if_false,zero_add,leaf,meet,
      disjoint_singleton_left,not_not,add_mul,one_mul] using n
  have regions : (patterns F U).card≤14800 := by
    rw [pattern_card]
    exact Nat.mul_le_mul_left 10 ((marks_le_labeled F U).trans (labels_le_21 F U us))
  have h₁ := (row_sum H (patterns F U) (3*ways 5)).trans (Nat.mul_le_mul_right _ regions)
  have h₂ := (row_sum H (attached F U B) (2*ways 6)).trans (Nat.mul_le_mul_right _ (attached_cap F U B us b))
  have h₃ := (row_sum H (attached F U A) (ways 6)).trans (Nat.mul_le_mul_right _ (attached_cap F U A us a))
  have all := sum_le_sum (s:=H) each
  rw [sum_add_distrib,sum_add_distrib] at all
  exact all.trans ((add_le_add (add_le_add h₁ h₂) h₃).trans (by decide))

noncomputable def charge (p : Prop) (v : Nat) : Nat := by classical exact if p then v else 0

theorem motif_row {F : Factor V C} {P Q : Pattern} (p : P∈family F) (q : Q∈family F) (ne : P≠Q) :
    (∑ R∈family F,coupon P Q R*(event (P∪Q∪R)).card) ≤
      charge (Separate P Q) (9420*ways 4)+charge (Wedge P Q) (44400*ways 5+153*ways 6) := by
  classical
  unfold charge
  by_cases s : Separate P Q
  · rw [if_pos s]
    exact (separate_row p q s).trans (Nat.le_add_right _ _)
  by_cases w : Wedge P Q
  · simpa [s,w] using wedge_row p q w
  simp only [single_or_empty ne s w,mul_zero,sum_const_zero,if_neg s,if_neg w,add_zero,le_refl]

end WildSieve.Thirty.Graph
