import CompanionCounts24
import DuplicatePairs24
import GraphTable24

namespace WildSieve.TwentyFour
open Finset SixCounts WildExact
local instance (priority := 2000) censusEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq

private theorem sum_owners (F : Factor V C) (w : Finset V → Nat) :
    (∑ S∈marks F univ,(owners F S).card*w S)=∑ a,∑ S∈candidates F a ∅ univ 6,w S := by
  classical
  have col (c : C) : (marks F univ).filter (fun Q => c∈owners F Q)=candidates F c ∅ univ 6 := by
    ext Q
    simp only [mem_filter,mark_mem,owner_mem,candidate_mem,empty_union,subset_univ,true_and]
    exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,c,h.2⟩,h.2⟩⟩
  have one (S) : (owners F S).card*w S=∑ c : C,if c∈owners F S then w S else 0 := by
    rw [←sum_filter,sum_const,nsmul_eq_mul]
    simp
  simp_rw [one]
  rw [sum_comm]
  apply sum_congr rfl
  intro c _
  rw [←sum_filter,col]

private theorem closed_of_three (F : Factor V C) (c : C) (S : Finset V) (sz : S.card=6) :
    Closed (F.f c) S ↔ Inside F c S=3 := by
  constructor
  · intro h
    have eq := closed_size (F.invol c) (F.moving c) h
    change S.card=2*Inside F c S at eq
    omega
  · intro n
    have total := paired_size (F.invol c) (F.moving c) S
    change (paired (F.f c) S).card=2*Inside F c S at total
    have eq : paired (F.f c) S=S := eq_of_subset_of_card_le (filter_subset _ _) (by omega)
    exact fun x hx => (mem_filter.mp (show x∈paired (F.f c) S from by rwa [eq])).2

private theorem tally_cuts (g : Coloring 24 23) (a c : C) (r : Fin 7) :
    (∑ S∈candidates (coloringFactor g) a ∅ univ 6,companion (Inside (coloringFactor g) c S) r)=
      ∑ i : Fin 4,graphCell g a c 6 3 i*companion i r := by
  classical
  let F : Factor V C := coloringFactor g
  let H := candidates F a ∅ univ 6
  have row (S) (h : S∈H) : (∑ i : Fin 4,if Inside F c S=i.val then companion i r else 0)=
      companion (Inside F c S) r := by
    have n := (inside_window F c S).2
    rw [(candidate_mem.mp h).2.1] at n
    let k : Fin 4 := ⟨Inside F c S,by omega⟩
    have test (i : Fin 4) : Inside F c S=i.val ↔ k=i := by simp [k,Fin.ext_iff]
    simp_rw [test]
    simp [k]
  change (∑ S∈H,_)=_
  rw [sum_congr rfl (fun S h => (row S h).symm),sum_comm]
  apply sum_congr rfl
  intro i _
  rw [←sum_filter,sum_const,nsmul_eq_mul,Nat.cast_id]
  congr 1
  change ((H.filter _).card)=(univ.filter _).card
  apply congrArg Finset.card
  ext S
  simp only [H,mem_filter,mem_univ,true_and,candidate_mem,subset_univ,empty_union]
  constructor
  · rintro ⟨⟨sz,cl⟩,num⟩
    exact ⟨sz,(closed_of_three F a S sz).mp cl,num⟩
  · rintro ⟨sz,three,num⟩
    exact ⟨⟨sz,(closed_of_three F a S sz).mpr three⟩,num⟩

/-- Exact census of ordered, color-labelled pairs of sixes, allowing a
repeated color and any prescribed intersection size. -/
theorem pair_census (g : Coloring 24 23) (r : Fin 7) :
    labeledPairs (coloringFactor g) r=
    ∑ a : C,∑ c : C,∑ i : Fin 4,graphCell g a c 6 3 i*companion i r := by
  classical
  let F : Factor V C := coloringFactor g
  have adj (S : Finset V) (sz : S.card=6) :
      (∑ B∈partners F r S,(owners F B).card)=∑ c : C,companion (Inside F c S) r := by
    let w (B : Finset V) := if (B∩S).card=r.val then 1 else 0
    have e := sum_owners F w
    simp only [w,mul_ite,Nat.mul_one,Nat.mul_zero,←sum_filter,sum_const,nsmul_eq_mul,Nat.cast_id] at e
    rw [sum_congr rfl (fun c _ => companion_sixes F c S sz r)] at e
    simpa only [partners,inter_comm S] using e
  unfold labeledPairs
  simp only [←mul_sum]
  rw [sum_owners]
  apply sum_congr rfl
  intro a _
  rw [sum_congr rfl (fun S h => adj S (candidate_mem.mp h).2.1),sum_comm]
  exact sum_congr rfl (fun c _ => tally_cuts g a c r)

#print axioms pair_census
end WildSieve.TwentyFour
