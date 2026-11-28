import MarkedMeans30

namespace WildSieve.Thirty.Graph
open Finset
local instance (priority := 2000) duplicateEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq
set_option maxRecDepth 10000

noncomputable def duplicateMean (F : Factor V C) (L : Finset V) (t : Fin 3) :=
  ∑ S∈marks F univ,(extra F S : ℚ)*markWeight L S t

theorem distinct_at_cut (F : Factor V C) (L : Finset V) (sz : L.card=12) (t : Fin 3) :
    conditionalMean F L t+duplicateMean F L t=∑ i : Fin 7,first t i*cutPopulation F L sz i := by
  rw [←labeled_mean,conditionalMean,duplicateMean,←sum_add_distrib]
  apply sum_congr rfl
  intro S hs
  have pos := (owners_bounds F hs).1
  have n : extra F S+1=(owners F S).card := Nat.sub_add_cancel pos
  have nr : (extra F S : ℚ)+1=(owners F S).card := by exact_mod_cast n
  rw [←nr,add_mul,one_mul,add_comm]

private theorem anchor_weight (F : Factor V C) (c : C) (S : Finset V) (sz : S.card=6) (t : Fin 3) :
    (∑ L∈anchors F c,markWeight L S t)=5005*duplicateWeight t (Inside F c S) := by
  have count := duplicate_anchors F c S sz t
  simp only [markWeight,inter_comm S,←sum_filter,sum_const,nsmul_eq_mul]
  rw [count,show Nat.choose 15 6=5005 by decide]
  ring

theorem duplicate_average (F : Factor V C) (t : Fin 3) :
    cutAvg F (fun L => duplicateMean F L t) =
      (∑ i : Fin 4,duplicateWeight t i*(duplicatePopulation F i : ℚ))/29 := by
  rw [duplicate_population_sum]
  unfold cutAvg anchorSum duplicateMean
  have per (c : C) : (∑ L∈anchors F c,∑ S∈marks F univ,(extra F S : ℚ)*markWeight L S t)=
      ∑ S∈marks F univ,(extra F S : ℚ)*(5005*duplicateWeight t (Inside F c S)) := by
    rw [sum_comm]
    apply sum_congr rfl
    intro S h
    rw [←mul_sum,anchor_weight F c S (mark_mem.mp h).2.1]
  simp_rw [per]
  rw [sum_comm]
  have terms (S : Finset V) : (∑ c,(extra F S : ℚ)*(5005*duplicateWeight t (Inside F c S))) =
      5005*((extra F S : ℚ)*∑ c,duplicateWeight t (Inside F c S)) := by
    simp only [←mul_sum]
    ring
  simp_rw [terms]
  rw [←mul_sum]
  ring

end WildSieve.Thirty.Graph
