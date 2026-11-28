import FilteredMoments
import MatchingSixes
import GraphSieve

namespace WildSieve.RootedSix15
open Finset WildExact
local instance (priority := 2000) {n : Nat} : DecidableEq (Fin n) :=
  (inferInstance : LinearOrder (Fin n)).toDecidableEq
variable {A C : Type} [LinearOrder A] [Fintype A] [Fintype C]

noncomputable def bad (F : Factor A C) (c : C) (U : Finset A) :=
  (candidates F c ∅ U 6).biUnion (localSeal U)

omit [Fintype A] [Fintype C] in
private theorem data {F : Factor A C} {c : C} {U Q : Finset A}
    (mem : Q∈candidates F c ∅ U 6) : Q⊆U ∧ Q.card=6 ∧ Closed (F.f c) Q := by
  simpa only [empty_union] using (candidate_mem.mp mem)

omit [Fintype C] in
private theorem no_cross {F : Factor A C} {c : C} {U Q R : Finset A} {L : Layout U}
    (qs : Q.card=6) (rs : R.card=6) (qc : Closed (F.f c) Q) (rc : Closed (F.f c) R)
    (ne : Q≠R) (q : L∈localSeal U Q) (r : L∈localSeal U R) : Disjoint Q R := by
  have three := intersect_sealed q r
  have both : Closed (F.f c) (Q∩R) := fun v hv =>
    mem_inter.mpr ⟨qc v (mem_inter.mp hv).1,rc v (mem_inter.mp hv).2⟩
  have even := closed_size (F.invol c) (F.moving c) both
  have strict : (Q∩R).card<6 := by
    by_contra! h
    have eqQ := Finset.eq_of_subset_of_card_le (inter_subset_left (s₁:=Q) (s₂:=R)) (qs ▸ h)
    have eqR := Finset.eq_of_subset_of_card_le (inter_subset_right (s₁:=Q) (s₂:=R)) (rs ▸ h)
    exact ne (eqQ.symm.trans eqR)
  rw [Finset.disjoint_iff_inter_eq_empty,←Finset.card_eq_zero]
  omega

omit [Fintype C] in
/-- A perfect matching can obstruct at most 91,000 layouts through ordinary six-sets on fifteen points. -/
theorem one_color (F : Factor A C) (c : C) (U : Finset A) (uc : U.card=15) :
    (bad F c U).card≤91000 := by
  classical
  let H := candidates F c ∅ U 6
  let N := fun Q : Finset A => candidates F c ∅ (U \ Q) 6
  let E := localSeal U
  have each (Q) (hq : Q∈H) : (E Q).card=2800 := by
    obtain ⟨qu,qs,_⟩ := data hq
    have z := local_seal_card U Q 2 3 qu qs (by omega)
    exact z.trans (by decide)
  have edges := ends_bound (F.invol c) U
  change 2*Inside F c U≤U.card at edges
  have how : H.card=(Inside F c U).choose 3 := candidate_pairs F c U 3
  by_cases small : Inside F c U≤6
  · have ct := Nat.choose_le_choose 3 small
    have cap : H.card≤20 := how ▸ ct
    have b := card_biUnion_le (s:=H) (t:=E)
    rw [sum_congr rfl each] at b
    change (H.biUnion E).card≤91000
    simp only [sum_const,nsmul_eq_mul,Nat.cast_id] at b
    omega
  have seven : Inside F c U=7 := by omega
  have hc : H.card=35 := by rw [how,seven]; decide
  have near (Q R : Finset A) (h : R∈N Q) : R∈H ∧ Disjoint R Q := by
    obtain ⟨ru,rs,rc⟩ := data h
    exact ⟨candidate_mem.mpr ⟨ru.trans sdiff_subset,rs,by simpa using rc⟩,
      disjoint_left.mpr (fun _ x y => (mem_sdiff.mp (ru x)).2 y)⟩
  have adj (Q) (hq : Q∈H) : N Q⊆H.erase Q := by
    intro R h
    obtain ⟨m,d⟩ := near Q R h
    exact mem_erase.mpr ⟨fun e => by subst R; have := disjoint_self.mp d; have sz := (data hq).2.1; simp_all,m⟩
  have deg (Q) (hq : Q∈H) : (N Q).card=4 := by
    obtain ⟨sub,six,cl⟩ := data hq
    have sp := split_inside F c (X:=∅) sub (by simp) (by simpa using cl)
    have pairs := closed_size (F.invol c) (F.moving c) cl
    change Q.card=2*Inside F c Q at pairs
    have four : Inside F c (U \ Q)=4 := by omega
    rw [show (N Q).card=(Inside F c (U \ Q)).choose 3 from candidate_pairs F c _ 3,four]; decide
  have pair (Q R) (hq : Q∈H) (hr : R∈N Q) : (E Q∩E R).card=100 := by
    obtain ⟨qu,qs,_⟩ := data hq
    obtain ⟨rh,d⟩ := near Q R hr
    obtain ⟨ru,rs,_⟩ := data rh
    exact (equal_joint U Q R 2 2 1 qu ru d.symm qs rs (by omega)).trans (by decide)
  have triple (Q R T) (hq : Q∈H) (hr : R∈N Q) (ht : T∈(N Q).erase R) :
      (E Q∩E R∩E T).card=0 := by
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_not_mem.mpr
    intro L h
    obtain ⟨notR,tn⟩ := mem_erase.mp ht
    obtain ⟨rh,rd⟩ := near Q R hr
    obtain ⟨th,td⟩ := near Q T tn
    obtain ⟨ru,rs,rc⟩ := data rh
    obtain ⟨tu,ts,tc⟩ := data th
    have tr := no_cross ts rs tc rc notR (mem_inter.mp h).2 (mem_inter.mp (mem_inter.mp h).1).2
    have dis : Disjoint (R∪T) Q := disjoint_union_left.mpr ⟨rd,td⟩
    have count := card_le_card (union_subset (union_subset ru tu) (data hq).1)
    rw [card_union_of_disjoint dis,card_union_of_disjoint tr.symm,rs,ts,(data hq).2.1,uc] at count
    omega
  have credit := overlap_credit H E N adj
  have o : (∑ Q∈H,(E Q).card)=98000 := by rw [sum_congr rfl each]; simp [hc]
  have tw : (∑ Q∈H,∑ R∈N Q,(E Q∩E R).card)=14000 := by
    calc
      _ = ∑ _∈H,400 := sum_congr rfl fun Q hq => by rw [sum_congr rfl (pair Q · hq)]; simp [deg Q hq]
      _ = _ := by simp [hc]
  have th : (∑ Q∈H,∑ R∈N Q,∑ T∈(N Q).erase R,(E Q∩E R∩E T).card)=0 :=
    sum_eq_zero fun Q hq => sum_eq_zero fun R hr => sum_eq_zero fun T ht => triple Q R T hq hr ht
  rw [o,tw,th] at credit
  change (H.biUnion E).card≤91000
  omega

/-- The same count applies to fifteen prescribed points in a factorization of any order. -/
theorem any_fifteen (F : Factor A C) (U : Finset A) (uc : U.card=15) :
    36400≤((univ : Finset (Layout U)) \ (univ : Finset C).biUnion (fun c => bad F c U)).card := by
  classical
  have per (c : C) : (bad F c U).card ≤ Inside F c U*13000 := by
    have cap := ends_bound (F.invol c) U
    change 2*Inside F c U≤U.card at cap
    by_cases seven : Inside F c U=7
    · rw [seven]; exact one_color F c U uc
    let H := candidates F c ∅ U 6
    have each (Q) (hq : Q∈H) : (localSeal U Q).card=2800 := by
      obtain ⟨sub,six,_⟩ := data hq
      exact (local_seal_card U Q 2 3 sub six (by omega)).trans (by decide)
    have loss := card_biUnion_le (s:=H) (t:=localSeal U)
    rw [sum_congr rfl each] at loss
    simp only [sum_const,nsmul_eq_mul,Nat.cast_id] at loss
    have sz : H.card=(Inside F c U).choose 3 := candidate_pairs F c U 3
    rw [sz] at loss
    have table : ∀ e : Fin 7,e.val.choose 3*2800≤e.val*13000 := by decide
    have small : Inside F c U<7 := by omega
    exact loss.trans (table ⟨Inside F c U,small⟩)
  have cap := card_biUnion_le (s:=(univ : Finset C)) (t:=fun c => bad F c U)
  have s := sum_le_sum (s:=(univ : Finset C)) (fun c _ => per c)
  rw [←sum_mul,sum_inside,uc,show (15 : Nat).choose 2=105 by decide] at s
  have total := card_sdiff_add_card_eq_card (subset_univ (univ.biUnion fun c => bad F c U))
  rw [card_univ,card_layout 5 U uc,show ways 5=1401400 by decide] at total
  omega

/-- The layout universe is the fifteen ordinary points of the actual coloring's completion. -/
theorem every_coloring (g : Coloring 15 15) :
    let F := coloringFactor (augment (n:=15) (by decide) g)
    let U := (univ : Finset (Fin 16)).erase (Fin.last 15)
    36400≤((univ : Finset (Layout U)) \ (univ : Finset (Fin 15)).biUnion (fun c => bad F c U)).card := by
  exact any_fifteen _ _ (by simp)

#print axioms any_fifteen
#print axioms every_coloring
end WildSieve.RootedSix15
