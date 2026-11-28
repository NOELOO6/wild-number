import OtherFrames30

namespace WildSieve.Thirty.Graph
open Finset
local instance (priority := 2000) secondEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq
set_option maxRecDepth 10000

def distinctPairCount (n m : Nat) (t k : Fin 3) := n*(m-if t=k then 1 else 0)

noncomputable def secondMean (F : Factor V C) (L : Finset V) (t k : Fin 3) :=
  sideAvg L (fun D => (distinctPairCount (sideHits F L D t).card (sideHits F L D k).card t k : ℚ))

private theorem other_erase (F : Factor V C) (L : Finset V) (D : Deck) (seen : D∈localSeal univ L)
    (t k : Fin 3) (P : Pattern) (hp : P∈present F L D t) :
    ((sideHits F L D k).erase (vertices P)).card=(sideHits F L D k).card-(if t=k then 1 else 0) := by
  have yes : vertices P∈sideHits F L D t := present_image F L D t seen ▸ mem_image_of_mem _ hp
  by_cases tk : t=k
  · subst k; simp [card_erase_of_mem yes]
  · have no : vertices P∉sideHits F L D k := by
      intro hk
      have a := (mem_filter.mp yes).2.1
      have b := (mem_filter.mp hk).2.1
      exact tk (Fin.ext (by have := t.isLt; have := k.isLt; omega))
    simp [erase_eq_of_not_mem no,tk]

private theorem expanded (F : Factor V C) (L : Finset V) (t k : Fin 3) :
    secondMean F L t k = (∑ P∈frames F L t,∑ Q∈marks F univ,(otherCount L P k Q : ℚ))/sideWays := by
  classical
  have per (D : Deck) (h : D∈localSeal univ L) :
      (distinctPairCount (sideHits F L D t).card (sideHits F L D k).card t k : ℚ) =
      ∑ P∈present F L D t,(((sideHits F L D k).erase (vertices P)).card : ℚ) := by
    have count := sum_present F L D t h (fun _ => (1 : ℚ))
    simp only [sum_const,nsmul_eq_mul,mul_one] at count
    rw [sum_congr rfl (fun P hp => congrArg (fun n : Nat => (n : ℚ)) (other_erase F L D h t k P hp))]
    simp only [distinctPairCount,Nat.cast_mul,sum_const,nsmul_eq_mul,count]
  unfold secondMean sideAvg localSum
  rw [sum_congr rfl per]
  congr 1
  simp only [present,sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro P _
  rw [←sum_filter]
  have subset : (localSeal univ L).filter (fun D => D∈frameEvent L P)=frameEvent L P := by ext D; simp [frameEvent]
  rw [subset]
  exact_mod_cast other_at_frame F L P k

theorem second_bound (F : Factor V C) (L : Finset V) (l : L.card=12) (t k : Fin 3) :
    secondMean F L t k ≤ frameAvg F L t (fun P => ∑ c,otherBill t k (signatureOf F c (regionOf F L t P))) := by
  rw [expanded,frameAvg]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact sum_le_sum (fun P hp => (other_distinct_le F L P k).trans_eq (other_labeled F L l t k P hp))

theorem complement_bound (F : Factor V C) (L : Finset V) (l : L.card=12) :
    secondMean F L 0 0+
      frameAvg F L 0 (fun P => ∑ c,complementCharge (signatureOf F c (regionOf F L 0 P))) ≤
      frameAvg F L 0 (fun P => ∑ c,otherBill 0 0 (signatureOf F c (regionOf F L 0 P)))+conditionalMean F L 0 := by
  rw [←frame_mass F L l 0,expanded]
  unfold frameAvg
  rw [←add_div,←add_div,←sum_add_distrib,←sum_add_distrib]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply sum_le_sum
  intro P hp
  simpa only [mul_one] using other_complement_le F L l P hp

#print axioms second_bound
#print axioms complement_bound
end WildSieve.Thirty.Graph
