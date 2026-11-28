import MomentGeometry36

namespace WildSieve.ThirtySix
open Finset
set_option maxHeartbeats 1600000
local instance (priority := 2000) motifVertexEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq

private theorem separate_three {F : Factor V C} {P Q R : Pattern}
    (p : P∈family F) (q : Q∈family F) (r : R∈family F)
    (ok : Triples (P∪Q∪R)) (pq : Disjoint P Q) (pr : Disjoint P R) (qr : Disjoint Q R) :
    (event (P∪Q∪R)).card≤symmetricCost P Q R := by
  have combined := disjoint_union_left.mpr ⟨pr,qr⟩
  have a : Separate P Q := (separate_iff P Q).mpr (supports_disjoint (ok.sub subset_union_left) pq)
  have b : Detached P Q R := (separate_iff _ _).mpr (supports_disjoint ok combined)
  rw [event_mass ok,card_union_of_disjoint combined,card_union_of_disjoint pq,
    pattern_size p,pattern_size q,pattern_size r,symmetricCost,charge_yes ⟨a,b⟩]
  change ways 6≤_
  omega

private theorem one_pair {F : Factor V C} {P Q R : Pattern} (p : P∈family F)
    (q : Q∈family F) (r : R∈family F) (ok : Triples (P∪Q∪R))
    (w : Wedge P Q) (pr : Disjoint P R) (qr : Disjoint Q R) :
    (event (P∪Q∪R)).card≤orientedCost P Q R := by
  have d := disjoint_union_left.mpr ⟨pr,qr⟩
  have b : Detached P Q R := (separate_iff _ _).mpr (supports_disjoint ok d)
  rw [event_mass ok,card_union_of_disjoint d,wedge_size p q w,pattern_size r,
    orientedCost,charge_yes ⟨w,b⟩]
  change ways 7≤_
  omega

private theorem two_pairs {F : Factor V C} {P Q R : Pattern} (p : P∈family F)
    (q : Q∈family F) (r : R∈family F) (ok : Triples (P∪Q∪R))
    (w : Wedge P Q) (pr : ¬Disjoint P R) (qr : Disjoint Q R) :
    (event (P∪Q∪R)).card≤orientedCost P Q R := by
  obtain ⟨A,ap⟩ := not_disjoint_iff_nonempty_inter.mp w.2.2
  obtain ⟨B,bp⟩ := not_disjoint_iff_nonempty_inter.mp pr
  obtain ⟨pa,qa⟩ := mem_inter.mp ap
  obtain ⟨pb,rb⟩ := mem_inter.mp bp
  have nb : B∉Q := fun h => disjoint_left.mp qr h rb
  have ab : A≠B := fun e => nb (e ▸ qa)
  have eq : ({A,B} : Pattern)=P := eq_of_subset_of_card_le
    (insert_subset pa (singleton_subset_iff.mpr pb)) (by rw [pattern_size p]; simp [ab])
  have ext : P⊆Q∪R := by
    rw [←eq]
    exact insert_subset (mem_union_left _ qa) (singleton_subset_iff.mpr (mem_union_right _ rb))
  have full : P∪Q∪R=Q∪R := by rw [union_assoc,union_eq_right.mpr ext]
  have leaf : JoinsLeaf P Q R := ⟨B,mem_sdiff.mpr ⟨pb,nb⟩,rb⟩
  rw [event_mass ok,full,card_union_of_disjoint qr,pattern_size q,pattern_size r,
    orientedCost,charge_yes (show Wedge P Q ∧ JoinsLeaf P Q R from ⟨w,leaf⟩) (ways 8)]
  change ways 8≤_
  omega

private theorem star_union (A B D Z : Finset V) :
    ({A,B} : Pattern)∪{A,D}∪{A,Z}={A,B,D,Z} := by
  ext X; simp only [mem_union,mem_insert,mem_singleton]; tauto

private theorem triangle_union (A B D : Finset V) :
    ({A,B} : Pattern)∪{A,D}∪{B,D}={A,B,D} := by
  ext X; simp only [mem_union,mem_insert,mem_singleton]; tauto

private theorem all_pairs {F : Factor V C} {P Q R : Pattern} (p : P∈family F)
    (q : Q∈family F) (r : R∈family F) (ok : Triples (P∪Q∪R))
    (w : Wedge P Q) (pr : ¬Disjoint P R) (qr : ¬Disjoint Q R)
    (rp : R≠P) (rq : R≠Q) : (event (P∪Q∪R)).card≤symmetricCost P Q R := by
  obtain ⟨A,B,D,pe,qe,ab,ad,bd⟩ := wedge_view p q w
  by_cases ar : A∈R
  · obtain ⟨Z,az,re⟩ := two_from (pattern_size r) ar
    have bz : B≠Z := by rintro rfl; exact rp (re.trans pe.symm)
    have dz : D≠Z := by rintro rfl; exact rq (re.trans qe.symm)
    have e : P∪Q∪R={A,B,D,Z} := by
      rw [pe,qe,re]; exact star_union A B D Z
    have sz : (P∪Q∪R).card=4 := by rw [e]; simp [ab,ad,az,bd,bz,dz]
    have center : JoinsCenter P Q R := ⟨A,mem_inter.mpr
      ⟨by rw [pe];simp,by rw [qe];simp⟩,ar⟩
    rw [event_mass ok,sz,symmetricCost,charge_yes (show Wedge P Q ∧ JoinsCenter P Q R from ⟨w,center⟩) (ways 8)]
    change ways 8≤_
    omega
  · have get (Z : Finset V) (inc : ¬Disjoint ({A,Z} : Pattern) R) : Z∈R := by
      obtain ⟨K,k⟩ := not_disjoint_iff_nonempty_inter.mp inc
      obtain ⟨side,h⟩ := mem_inter.mp k
      rcases mem_insert.mp side with z|z
      · exact (ar (z ▸ h)).elim
      · exact mem_singleton.mp z ▸ h
    have br := get B (pe ▸ pr)
    have dr := get D (qe ▸ qr)
    have re : ({B,D} : Pattern)=R := eq_of_subset_of_card_le
      (insert_subset br (singleton_subset_iff.mpr dr)) (by rw [pattern_size r]; simp [bd])
    have e : P∪Q∪R={A,B,D} := by
      rw [pe,qe,←re]; exact triangle_union A B D
    have sz : (P∪Q∪R).card=3 := by rw [e]; simp [ab,ad,bd]
    have tri : ClosesTriangle P Q R := by
      unfold ClosesTriangle
      rw [pe,qe,←re]
      ext X
      simp only [mem_union,mem_sdiff,mem_insert,mem_singleton]
      constructor
      · rintro (rfl|rfl) <;> simp [ab.symm,ad.symm,bd,bd.symm]
      · tauto
    rw [event_mass ok,sz,symmetricCost,charge_yes (show Wedge P Q ∧ ClosesTriangle P Q R from ⟨w,tri⟩) (ways 9)]
    change ways 9≤_
    omega

/-- Classify three distinct conflict edges by the intersections of their
two-element block sets. The asymmetric cases admit three cyclic orders. -/
theorem motif_charge {F : Factor V C} {P Q R : Pattern} (p : P∈family F) (q : Q∈family F)
    (r : R∈family F) (pq : P≠Q) (pr : P≠R) (qr : Q≠R) :
    (event (P∪Q∪R)).card ≤ symmetricCost P Q R+orientedCost P Q R+
      orientedCost Q R P+orientedCost R P Q := by
  classical
  by_cases ok : Triples (P∪Q∪R)
  swap
  · rw [event_empty ok]; exact Nat.zero_le _
  have cyc : Q∪R∪P=P∪Q∪R := by ac_rfl
  have rev : R∪P∪Q=P∪Q∪R := by ac_rfl
  have second : Triples (Q∪R∪P) := cyc.symm ▸ ok
  have third : Triples (R∪P∪Q) := rev.symm ▸ ok
  have ab (a : ¬Disjoint P Q) : Wedge P Q := ⟨pq,ok.sub subset_union_left,a⟩
  have bc (b : ¬Disjoint Q R) : Wedge Q R := ⟨qr,second.sub subset_union_left,b⟩
  have ca (c : ¬Disjoint R P) : Wedge R P := ⟨pr.symm,third.sub subset_union_left,c⟩
  have sym {X Y : Pattern} (h : ¬Disjoint X Y) : ¬Disjoint Y X := fun d => h d.symm
  by_cases a : Disjoint P Q <;> by_cases b : Disjoint Q R <;> by_cases c : Disjoint R P
  · have h := separate_three p q r ok a c.symm b; omega
  · have h := one_pair r p q third (ca c) b.symm a; rw [rev] at h; omega
  · have h := one_pair q r p second (bc b) a.symm c; rw [cyc] at h; omega
  · have h := two_pairs r p q third (ca c) (sym b) a; rw [rev] at h; omega
  · have h := one_pair p q r ok (ab a) c.symm b; omega
  · have h := two_pairs p q r ok (ab a) (sym c) b; omega
  · have h := two_pairs q r p second (bc b) (sym a) c; rw [cyc] at h; omega
  · have h := all_pairs p q r ok (ab a) (sym c) b pr.symm qr.symm; omega

end WildSieve.ThirtySix
