import GraphRegions24
import CycleData24
import MatchingSpectrum

namespace WildSieve.TwentyFour
open Finset SixCounts
local instance (priority := 2000) companionEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq

private def contribution (f : V → V) (S : Finset V) (v : V) : Nat :=
  (if v∈S then 1 else 0)+(if f v∈S then 1 else 0)

private def inventory (i : Nat) : Multiset Nat :=
  Multiset.replicate (6+i) 0 + Multiset.replicate (6-2*i) 1 + Multiset.replicate i 2

private theorem edge_inventory (F : Factor V C) (c : C) (S : Finset V) (sz : S.card=6) :
    (lowerEnds (F.f c) univ).val.map (contribution (F.f c) S)=inventory (Inside F c S) := by
  let f := F.f c
  let B := lowerEnds f univ
  let i := Inside F c S
  let bin (n : Nat) := B.filter fun v => contribution f S v=n
  have both : bin 2=lowerEnds f S := by
    ext v; by_cases a : v∈S <;> by_cases b : f v∈S <;> simp [bin,B,contribution,lowerEnds,a,b]
  have neither : bin 0=lowerEnds f Sᶜ := by
    ext v; by_cases a : v∈S <;> by_cases b : f v∈S <;> simp [bin,B,contribution,lowerEnds,a,b]
  have nums := free_pair_size (F.invol c) (F.moving c) S
  change 2*Inside F c Sᶜ=Sᶜ.card-(S.card-2*i) at nums
  rw [card_compl,Fintype.card_fin,sz] at nums
  have top : i≤3 := by have h := (inside_window F c S).2; rw [sz] at h; dsimp [i]; omega
  have zero : (bin 0).card=6+i := by rw [neither]; change Inside F c Sᶜ=_; omega
  have two : (bin 2).card=i := congrArg Finset.card both
  have width (v) : contribution f S v<3 := by unfold contribution; split <;> split <;> decide
  have count := card_eq_sum_card_fiberwise (s:=B) (t:=range 3) (f:=contribution f S)
    (fun v _ => mem_range.mpr (width v))
  change B.card=∑ n∈range 3,(bin n).card at count
  have bc : B.card=12 := full_pairs F c
  simp only [sum_range_succ,sum_range_zero,Nat.zero_add,zero,two,bc] at count
  have one : (bin 1).card=6-2*i := by omega
  apply Multiset.ext.mpr
  intro n
  rw [Multiset.count_map]
  change (B.filter (fun v => n=contribution f S v)).card=_
  have eq : B.filter (fun v => n=contribution f S v)=bin n := by ext v; simp only [bin,mem_filter]; exact and_congr_right (fun _ => eq_comm)
  rw [eq]
  change (bin n).card=(inventory i).count n
  rcases n with _|n
  · simpa [inventory,Multiset.count_replicate] using zero
  rcases n with _|n
  · simpa [inventory,Multiset.count_replicate] using one
  rcases n with _|n
  · simpa [inventory,Multiset.count_replicate] using two
  have nil : bin (n+3)=∅ := eq_empty_iff_forall_not_mem.mpr fun v h => by
    have := (mem_filter.mp h).2
    have b := width v
    omega
  simp [nil,inventory,Multiset.count_replicate]

private theorem count_sum (M : Multiset (Multiset Bool)) :
    M.sum.count true=(M.map (Multiset.count true)).sum := by
  induction M using Multiset.induction with
  | empty => simp
  | cons a s ih => simp [ih]

set_option maxRecDepth 15000 in
set_option maxHeartbeats 1000000 in
private theorem small_table : ∀ i : Fin 4,∀ r : Fin 7,
    ((((inventory i).powersetCard 3).map Multiset.sum).count r.val)=companion i r := by decide

/-- For any marked or unmarked six-set and any color, the overlap table counts
the actual six-sets closed by that color. -/
theorem companion_sixes (F : Factor V C) (c : C) (S : Finset V) (sz : S.card=6) (r : Fin 7) :
    ((candidates F c ∅ univ 6).filter (fun Q => (Q∩S).card=r.val)).card=companion (Inside F c S) r := by
  let tag (v : V) := decide (v∈S)
  have weight (Q : Finset V) : (Q.val.map tag).count true=(Q∩S).card := by
    rw [Multiset.count_map]
    apply congrArg Multiset.card
    change (Q.filter (fun v => true=tag v)).val=(Q∩S).val
    congr 1
    ext v
    simp [tag,eq_comm]
  have per (v : V) : (pairTag (F.f c) tag v).count true=contribution (F.f c) S v := by
    by_cases a : v∈S <;> by_cases b : F.f c v∈S <;> simp [pairTag,tag,contribution,a,b]
  have data := congrArg (Multiset.map (Multiset.count true)) (matching_spectrum F c univ 3 tag)
  simp only [Multiset.map_map,Function.comp_def,weight,count_sum] at data
  have bag := congrArg (Multiset.map (fun M : Multiset Nat => M.sum))
    (Multiset.powersetCard_map (Multiset.count true) 3 ((lowerEnds (F.f c) univ).val.map (pairTag (F.f c) tag)))
  simp only [Multiset.map_map,Function.comp_def,per,edge_inventory F c S sz] at bag
  rw [←bag] at data
  have eq := congrArg (Multiset.count r.val) data
  rw [Multiset.count_map] at eq
  have i : Inside F c S<4 := by have h := (inside_window F c S).2; rw [sz] at h; omega
  apply Eq.trans _ (small_table ⟨_,i⟩ r)
  apply Eq.trans _ eq
  change _=((candidates F c ∅ univ 6).filter (fun Q => r.val=(Q∩S).card)).card
  apply congrArg Finset.card
  ext Q
  simp only [mem_filter]
  exact and_congr_right (fun _ => eq_comm)

#print axioms companion_sixes
end WildSieve.TwentyFour
