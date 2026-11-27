import TripleSeal42
import OverlapCredit
namespace WildSieve.FortyTwo
open Finset
set_option maxHeartbeats 3000000
local instance (priority := 2000) shortVertexEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq

private def singleMass := 10*ways 12
private def pairMass := 100*ways 10
private def thirdMass := 7525*(1000*ways 8)+1480*(10*ways 9)

/-- The worst bound occurs at the largest possible number of distinct marks. -/
private theorem arithmetic (a n z : Nat) (cap : a≤54530)
    (pairs : a*20230+a*a≤54530*a+n)
    (credit : 6*z+3*(n*pairMass)≤6*(a*singleMass)+n*thirdMass) :
    1000*z≤723*ways 14 := by
  let d := 54530-a
  have total : a+d=54530 := by dsimp [d];omega
  have row : a*20230≤a*d+n := by
    have eq : 54530*a=a*a+a*d := by rw [←total,Nat.add_mul,Nat.mul_comm d a]
    omega
  have top := Nat.mul_le_mul_right d cap
  have price : 54530*20230≤n+(54530+20230)*d := by
    have prod := congrArg (·*20230) total
    simp only [Nat.add_mul] at prod
    omega
  have rates : thirdMass<3*pairMass := by decide
  have lift := Nat.mul_le_mul_left (3*pairMass-thirdMass) price
  have d1 : 3*pairMass=thirdMass+(3*pairMass-thirdMass) := by omega
  have ac := congrArg (·*(6*singleMass)) total
  simp only [Nat.add_mul] at ac
  norm_num [pairMass,thirdMass,singleMass,ways,Nat.fast_choose] at credit lift ac ⊢
  omega

/-- Fewer than 72.3 percent (rounded upward) of all partitions are lost to
six-point components in an arbitrary coloring of K42. -/
theorem short_budget (F : Factor V C) :
    1000*((marks F univ).biUnion hit).card≤723*ways 14 := by
  classical
  let H := marks F univ
  let N (T : Finset V) := marks F Tᶜ
  let count := ∑ T∈H,(N T).card
  have adj (T) (ht : T∈H) : N T⊆H.erase T := by
    intro S hs
    obtain ⟨sub,s,c⟩ := mark_mem.mp hs
    have sz := (mark_mem.mp ht).2.1
    refine mem_erase.mpr ⟨?_,mark_mem.mpr ⟨subset_univ _,s,c⟩⟩
    rintro rfl
    obtain ⟨x,h⟩ := card_pos.mp (by omega : 0<S.card)
    exact mem_compl.mp (sub h) h
  have bound := overlap_credit H hit N adj
  have singles (T) (ht : T∈H) : (hit T).card=singleMass :=
    local_seal_card univ T 2 12 (subset_univ _) (mark_mem.mp ht).2.1 (by
      rw [card_univ,Fintype.card_fin,(mark_mem.mp ht).2.1])
  have pairs (T) (ht : T∈H) : (∑ S∈N T,(hit T∩hit S).card)=(N T).card*pairMass := by
    have each (S) (hs : S∈N T) : (hit T∩hit S).card=pairMass := double_card T S
      (mark_mem.mp ht).2.1 (mark_mem.mp hs).2.1
      (disjoint_left.mpr (fun _ h h' => mem_compl.mp ((mark_mem.mp hs).1 h') h))
    rw [sum_congr rfl each,sum_const];rfl
  have trips (T) (ht : T∈H) : (∑ S∈N T,∑ Q∈(N T).erase S,(hit T∩hit S∩hit Q).card)≤(N T).card*thirdMass := by
    simpa only [sum_const,nsmul_eq_mul,Nat.cast_id] using
      sum_le_sum (s:=N T) (fun S h => triple_budget F T S (mark_mem.mp ht).2.1 h)
  have three := sum_le_sum trips
  rw [←sum_mul] at three
  rw [sum_congr rfl singles,sum_const,nsmul_eq_mul,sum_congr rfl pairs,←sum_mul] at bound
  have minD := sum_le_sum (s:=H) (fun T h => disjoint_lower F T (mark_mem.mp h).2.1)
  change (∑ _∈H,(20230+H.card))≤∑ T∈H,(54530+(N T).card) at minD
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,sum_add_distrib] at minD
  rw [Nat.mul_add] at minD
  apply arithmetic H.card count _ (total_marks F)
  · simpa [Nat.mul_comm] using minD
  · exact bound.trans (Nat.add_le_add_left three _)
end WildSieve.FortyTwo
