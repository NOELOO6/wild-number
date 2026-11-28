import TripleMotifs36
import ChargeBounds36
import OverlapCredit

namespace WildSieve.ThirtySix
set_option maxHeartbeats 1600000
open Finset
open scoped Classical
local instance (priority := 2000) momentVertexEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq

private theorem pair_mass {F : Factor V C} {P Q : Pattern} (p : P∈family F) (q : Q∈family F)
    (diff : P≠Q) : (event P∩event Q).card=charge (Separate P Q) (ways 8)+charge (Wedge P Q) (ways 9) := by
  classical
  rw [event_union]
  by_cases s : Separate P Q
  · have dis := (separate_iff _ _).mp s
    have b := blocks_disjoint (pattern_mem.mp p).1 dis
    have w : ¬Wedge P Q := fun v => v.2.2 b
    rw [event_mass ((pattern_mem.mp p).1.combine (pattern_mem.mp q).1 dis),
      card_union_of_disjoint b,pattern_size p,pattern_size q,charge_yes s,charge_no w,add_zero]
  by_cases ok : Triples (P∪Q)
  · have overlap : ¬Disjoint P Q := fun h => s ((separate_iff _ _).mpr (supports_disjoint ok h))
    have w : Wedge P Q := ⟨diff,ok,overlap⟩
    rw [event_mass ok,wedge_size p q w,charge_no s,charge_yes w,zero_add]
  · have w : ¬Wedge P Q := fun h => ok h.2.1
    rw [event_empty ok,charge_no s,charge_no w,zero_add]

private theorem tally_wide (F : Factor V C) (v : Nat) :
    (∑ P∈family F,∑ Q∈family F,charge (Separate P Q) v)=(wide F).card*v := by
  classical
  rw [←sum_product']
  simp only [charge,←sum_filter,sum_const,nsmul_eq_mul,Nat.cast_id]
  congr 1

private theorem tally_touching (F : Factor V C) (v : Nat) :
    (∑ P∈family F,∑ Q∈family F,charge (Wedge P Q) v)=(touching F).card*v := by
  classical
  rw [←sum_product']
  simp only [charge,←sum_filter,sum_const,nsmul_eq_mul,Nat.cast_id]
  congr 1

private theorem second_moment (F : Factor V C) :
    (∑ P∈family F,∑ Q∈(family F).erase P,(event P∩event Q).card)=
      (wide F).card*ways 8+(touching F).card*ways 9 := by
  classical
  let H := family F
  let f (P Q : Pattern) := charge (Separate P Q) (ways 8)+charge (Wedge P Q) (ways 9)
  have row (P : Pattern) (p : P∈H) : (∑ Q∈H.erase P,(event P∩event Q).card)=∑ Q∈H,f P Q := by
    have no : ¬Separate P P := by
      intro s
      have empty := disjoint_self.mp ((separate_iff _ _).mp s)
      have c := (mark_mem.mp (pattern_mem.mp p).2).2.1
      rw [empty] at c
      contradiction
    have diag : f P P=0 := by simp [f,no,Wedge]
    have all := sum_erase_add H (f P) p
    rw [diag,add_zero] at all
    exact (sum_congr rfl (fun Q h => pair_mass p (mem_erase.mp h).2 (mem_erase.mp h).1.symm)).trans all
  rw [sum_congr rfl row]
  simp only [f,sum_add_distrib,H,tally_wide,tally_touching]

private theorem cycle_sum (S : Finset Pattern) (f : Pattern → Pattern → Pattern → Nat) :
    (∑ P∈S,∑ Q∈S,∑ R∈S,f Q R P)=∑ P∈S,∑ Q∈S,∑ R∈S,f P Q R := by
  rw [sum_comm]
  apply sum_congr rfl
  intro Q _
  rw [sum_comm]

def wideThird := 29000*ways 6
def touchThird := 3*(47580*ways 7)+320*ways 8+ways 9

private theorem third_moment (F : Factor V C) :
    (∑ P∈family F,∑ Q∈(family F).erase P,∑ R∈((family F).erase P).erase Q,
      (event P∩event Q∩event R).card)≤(wide F).card*wideThird+(touching F).card*touchThird := by
  classical
  let H := family F
  let f (P Q R : Pattern) := symmetricCost P Q R+orientedCost P Q R+orientedCost Q R P+orientedCost R P Q
  have per (P) (p : P∈H) (Q) (q : Q∈H.erase P) (R) (r : R∈(H.erase P).erase Q) :
      (event P∩event Q∩event R).card≤f P Q R := by
    obtain ⟨qp,qh⟩ := mem_erase.mp q
    obtain ⟨rq,r'⟩ := mem_erase.mp r
    obtain ⟨rp,rh⟩ := mem_erase.mp r'
    rw [event_union,event_union]
    exact motif_charge p qh rh qp.symm rp.symm rq.symm
  have bound := sum_le_sum (s:=H) (fun P p => sum_le_sum (s:=H.erase P) (fun Q q =>
    sum_le_sum (s:=(H.erase P).erase Q) (fun R r => per P p Q q R r)))
  have lift (P) (Q : Pattern) : (∑ R∈(H.erase P).erase Q,f P Q R)≤∑ R∈H,f P Q R :=
    sum_le_sum_of_subset_of_nonneg (erase_subset _ _ |>.trans (erase_subset _ _)) (fun _ _ _ => Nat.zero_le _)
  have more (P : Pattern) : (∑ Q∈H.erase P,∑ R∈(H.erase P).erase Q,f P Q R)≤∑ Q∈H,∑ R∈H,f P Q R :=
    (sum_le_sum (fun Q _ => lift P Q)).trans (sum_le_sum_of_subset_of_nonneg (erase_subset _ _)
      (fun _ _ _ => Nat.zero_le _))
  have total := bound.trans (sum_le_sum (fun P _ => more P))
  have turn := cycle_sum H orientedCost
  have turn' := cycle_sum H (fun P Q R => orientedCost Q R P)
  simp only [f,sum_add_distrib] at total
  dsimp only [H] at total turn turn'
  have sym := sum_le_sum (s:=H) (fun P p => sum_le_sum (s:=H) (fun Q q => symmetric_row p q))
  have ori := sum_le_sum (s:=H) (fun P p => sum_le_sum (s:=H) (fun Q q => oriented_row p q))
  simp only [H,sum_add_distrib,tally_wide,tally_touching] at sym ori
  change _≤(wide F).card*(29000*ways 6)+(touching F).card*(3*(47580*ways 7)+320*ways 8+ways 9)
  norm_num [ways,Nat.fast_choose] at sym ori total ⊢
  rw [turn',turn] at total
  apply total.trans
  apply (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add sym ori) ori) ori).trans
  omega

/-- The cardinality bound for partitions lost to a six-point cut retains
the number of repeated six-set labels as a parameter for the larger cuts. -/
theorem short_moment (F : Factor V C) :
    12*((family F).biUnion event).card+
      5*((wide F).card*ways 8+(touching F).card*ways 9)≤
      12*(10*(marks F univ).card*ways 10)+
      ((wide F).card*wideThird+(touching F).card*touchThird) := by
  classical
  let H := family F
  have h := overlap_credit_twelve H event (fun P => H.erase P) (fun _ _ => Subset.refl _)
  have one (P : Pattern) (p : P∈H) : (event P).card=ways 10 := by
    rw [event_mass (pattern_mem.mp p).1,pattern_size p]
  rw [sum_congr rfl one,sum_const,nsmul_eq_mul,second_moment F] at h
  change _≤12*((family F).card*ways 10)+_ at h
  rw [pattern_card] at h
  exact h.trans (Nat.add_le_add_left (third_moment F) _)

end WildSieve.ThirtySix
