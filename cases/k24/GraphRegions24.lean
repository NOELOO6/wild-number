import Concentration24
import SixCounts

namespace WildSieve.TwentyFour
open Finset SixCounts
abbrev V := Fin 24
abbrev C := Fin 23
local instance (priority := 2000) regionEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq

/-- Ordered pairs of distinct marked sixes covering exactly the given region. -/
noncomputable def rowPairs (F : Factor V C) (U A : Finset V) :=
  (marks F U).filter fun B => A∪B=U ∧ A≠B
noncomputable def pairsOn (F : Factor V C) (U : Finset V) :=
  ∑ A∈marks F U,(rowPairs F U A).card

private theorem row_choices (F : Factor V C) (U A : Finset V) (h : A∈marks F U) :
    (rowPairs F U A).card≤(6 : Nat).choose (12-U.card) := by
  classical
  obtain ⟨asub,a,_⟩ := mark_mem.mp h
  let chart (B : Finset V) := A∩B
  apply le_trans _ (show (A.powersetCard (12-U.card)).card=(6 : Nat).choose (12-U.card) by rw [card_powersetCard,a]).le
  apply card_le_card_of_injOn chart
  · intro B hb
    obtain ⟨base,eq,_⟩ := mem_filter.mp hb
    obtain ⟨_,b,_⟩ := mark_mem.mp base
    have sum := card_union_add_card_inter A B
    rw [eq,a,b] at sum
    exact mem_powersetCard.mpr ⟨inter_subset_left,by change (A∩B).card=_; omega⟩
  · intro B hb Z hz same
    obtain ⟨_,ub,_⟩ := mem_filter.mp hb
    obtain ⟨_,uz,_⟩ := mem_filter.mp hz
    change A∩B=A∩Z at same
    ext x
    by_cases ax : x∈A
    · simpa [ax] using (show x∈A∩B ↔ x∈A∩Z by rw [same])
    · simpa [ax] using (show x∈A∪B ↔ x∈A∪Z by rw [ub,uz])

theorem pairs_on_cap (F : Factor V C) (U : Finset V) (u : Nat) (sz : U.card=u)
    (small : u=9 ∨ u=12) : pairsOn F U≤maxPairs u (labeled F U) := by
  classical
  let H := marks F U
  have bound := sum_le_sum (s:=H) (fun A h => row_choices F U A h)
  change pairsOn F U≤_ at bound
  rw [sum_const,nsmul_eq_mul,sz] at bound
  have extra (A) (ha : A∈H) : (rowPairs F U A).card≤H.card-1 := by
    rw [←card_erase_of_mem ha]
    exact card_le_card (fun _ h => mem_erase.mpr ⟨(mem_filter.mp h).2.2.symm,(mem_filter.mp h).1⟩)
  have others := sum_le_sum extra
  change pairsOn F U≤_ at others
  rw [sum_const,nsmul_eq_mul] at others
  have count : H.card≤labeled F U := marks_le_labeled F U
  rcases small with rfl|rfl
  · have twenty : (6 : Nat).choose (12-9)=20 := by decide
    rw [twenty] at bound
    simp only [maxPairs,show (9 : Nat)≠12 by decide,if_false]
    apply Nat.le_min.mpr
    exact ⟨bound.trans (by simpa only [Nat.mul_comm] using Nat.mul_le_mul_right 20 count),
      others.trans (Nat.mul_le_mul count (Nat.sub_le_sub_right count 1))⟩
  · simp only [maxPairs,if_true]
    simpa only [Nat.sub_self,show Nat.choose 6 0=1 by decide,Nat.mul_one,Nat.cast_id] using bound.trans (by
      simpa only [Nat.sub_self,show Nat.choose 6 0=1 by decide,Nat.mul_one,Nat.cast_id] using count)

def popAt (F : Factor V C) (U : Finset V) (i : Nat) := (univ.filter (fun c : C => Inside F c U=i)).card

def population (F : Factor V C) (U : Finset V) := (List.range (U.card/2+1)).map (popAt F U)

private theorem pop_sum (F : Factor V C) (U : Finset V) (f : Nat → Nat) :
    ∑ i∈range (U.card/2+1), f i*popAt F U i=∑ c, f (Inside F c U) := by
  classical
  have row (i : Nat) : f i*popAt F U i=∑ c : C, if Inside F c U=i then f i else 0 := by
    rw [←sum_filter,sum_const,nsmul_eq_mul,Nat.mul_comm]
    rfl
  simp_rw [row]
  rw [sum_comm]
  apply sum_congr rfl
  intro c _
  have valid := (inside_window F c U).2
  simp [show Inside F c U<U.card/2+1 by omega]

private theorem list_sum (k : Nat) (f : Nat → Nat) :
    ((List.range k).map f).sum=∑ i∈range k,f i := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.range_succ,sum_range_succ,ih]

private theorem weight_list (f : Nat → Nat) (k : Nat) :
    internalPairs (((List.range k).map f).reverse)=∑ i∈range k,i*f i := by
  induction k with
  | zero => simp [internalPairs]
  | succ k ih => simp [List.range_succ,internalPairs,ih,sum_range_succ,Nat.add_comm]

private theorem six_population (F : Factor V C) (U : Finset V) (d : Nat) :
    sixes (population F U) d=∑ c, (Inside F c U+d).choose 3 := by
  unfold sixes
  have eq (i) (hi : i∈List.range (population F U).length) : (population F U)[i]! = popAt F U i := by
    have mem := List.mem_range.mp hi
    rw [getElem!_pos (c:=population F U) (i:=i) mem]
    simp [population]
  have rewrite : ((List.range (population F U).length).map fun i =>
      (population F U)[i]!*(i+d).choose 3) = (List.range (U.card/2+1)).map
        (fun i => (i+d).choose 3*popAt F U i) := by
    have len : (population F U).length=U.card/2+1 := by simp [population]
    conv_rhs => rw [←len]
    apply List.map_congr_left
    intro i hi
    rw [eq _ hi,Nat.mul_comm]
  rw [rewrite,list_sum,pop_sum]

/-- The certified quadratic controls the actual number of pairs of six-sets
in a region, times its excess number of complementary labels. -/
theorem regional_concentration (F : Factor V C) (U : Finset V) (u b : Nat)
    (sz : U.card=u) (job : (u,b)∈jobs) :
    ((pairsOn F U*(labeled F Uᶜ-b) : Nat) : ℚ)≤polynomial u b (population F U) := by
  have types : u=12 ∨ u=9 := by
    simp only [jobs,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at job
    rcases job with h|h|h <;> omega
  have small : u≤12 := by omega
  let h := population F U
  have colors : h.reverse.sum=23 := by
    have s := pop_sum F U (fun _ => 1)
    simpa [h,population,list_sum] using s
  have num : internalPairs h.reverse=u.choose 2 := by
    rw [show h=(List.range (U.card/2+1)).map (popAt F U) from rfl,weight_list,pop_sum]
    rw [sum_inside,sz]
  have actual := concentration u b job h.reverse (by simp [h,population,sz]) colors num
  rw [List.reverse_reverse] at actual
  have left : sixes h 0=labeled F U := by simpa [h,labeled] using six_population F U 0
  have one (c : C) : Inside F c U+(12-u)=Inside F c Uᶜ := by
    have t := free_pair_size (F.invol c) (F.moving c) U
    change 2*Inside F c Uᶜ=Uᶜ.card-(U.card-2*Inside F c U) at t
    rw [card_compl,Fintype.card_fin,sz] at t
    have lo := (inside_window F c U).2
    rw [sz] at lo
    omega
  have right : sixes h (12-u)=labeled F Uᶜ := by
    rw [show h=population F U by rfl,six_population]
    simp only [one,labeled]
  rw [left,right] at actual
  exact le_trans (by exact_mod_cast Nat.mul_le_mul_right (labeled F Uᶜ-b) (pairs_on_cap F U u sz types.symm)) actual

#print axioms regional_concentration
end WildSieve.TwentyFour
