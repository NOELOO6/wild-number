import Sampling30

namespace WildSieve.Thirty.Graph
open Finset
local instance (priority := 2000) meanEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq
set_option maxRecDepth 12000

def markWeight (L Q : Finset V) (t : Fin 3) : ℚ :=
  if (Q∩L).card=6-3*t.val then factor 12 18 t else 0

noncomputable def conditionalMean (F : Factor V C) (L : Finset V) (t : Fin 3) :=
  ∑ Q∈marks F univ,markWeight L Q t

theorem weight_nonneg (L Q : Finset V) (t : Fin 3) : 0≤markWeight L Q t := by
  have h : ∀ j : Fin 3,0≤factor 12 18 j := by native_decide
  unfold markWeight
  split <;> first | exact h t | exact le_rfl

theorem split_mark_weight (L Q : Finset V) (l : L.card=12) (q : Q.card=6) (t : Fin 3) :
    (if (Q∩L).card=6-3*t.val then ((localSeal univ L∩localSeal univ Q).card : ℚ) else 0) =
      markWeight L Q t*sideWays := by
  unfold markWeight
  split
  next yes =>
    rw [joint_seal_ways _ _ _ (subset_univ _) (subset_univ _),card_sdiff (subset_univ _),card_univ,
      Fintype.card_fin,l,yes]
    have sub := card_sdiff_add_card_inter Q L
    rw [q,yes] at sub
    have all : ∀ j : Fin 3,j=0 ∨ j=1 ∨ j=2 := by decide
    have free : (Q \ L).card=3*t.val := by have := t.isLt; omega
    rw [free]
    rcases all t with rfl|rfl|rfl <;> native_decide
  next => simp

private theorem candidates_by_owner (F : Factor V C) (c : C) :
    (marks F univ).filter (fun Q => c∈owners F Q)=candidates F c ∅ univ 6 := by
  ext Q
  simp only [mem_filter,mark_mem,owner_mem,candidate_mem,empty_union,subset_univ,true_and]
  exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,c,h.2⟩,h.2⟩⟩

theorem owner_weight_sum (F : Factor V C) (w : Finset V → ℚ) :
    (∑ Q∈marks F univ,(owners F Q).card*w Q)=∑ c,∑ Q∈candidates F c ∅ univ 6,w Q := by
  classical
  have per (Q : Finset V) : (owners F Q).card*w Q =
      ∑ c : C, if c∈owners F Q then w Q else 0 := by
    rw [←sum_filter]
    simp [nsmul_eq_mul]
  simp_rw [per]
  rw [sum_comm]
  apply sum_congr rfl
  intro c _
  rw [←sum_filter,candidates_by_owner]

theorem owners_bounds (F : Factor V C) {Q : Finset V} (h : Q∈marks F univ) :
    1≤(owners F Q).card ∧ (owners F Q).card≤5 := by
  obtain ⟨_,sz,c,cl⟩ := mark_mem.mp h
  obtain ⟨x,hx⟩ := card_pos.mp (show 0<Q.card by omega)
  have sub : (owners F Q).image (fun j => F.f j x)⊆Q.erase x := by
    intro y hy
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hy
    exact mem_erase.mpr ⟨(F.moving j x).symm,owner_mem.mp hj x hx⟩
  have bound := card_le_card sub
  rw [card_image_of_injective _ (F.unique x),card_erase_of_mem hx,sz] at bound
  exact ⟨card_pos.mpr ⟨c,owner_mem.mpr cl⟩,bound⟩

theorem color_first (F : Factor V C) (c : C) (L : Finset V) (sz : L.card=12) (t : Fin 3) :
    (∑ Q∈candidates F c ∅ univ 6,markWeight L Q t)=first t (Inside F c L) := by
  have positive : (sideWays : ℚ)≠0 := by decide
  apply mul_right_cancel₀ positive
  rw [sum_mul]
  have raw := labeled_first F c L sz t
  refine Eq.trans (sum_congr rfl (fun Q h => ?_)) raw
  exact (split_mark_weight L Q sz (candidate_mem.mp h).2.1 t).symm

theorem labeled_mean (F : Factor V C) (L : Finset V) (sz : L.card=12) (t : Fin 3) :
    (∑ Q∈marks F univ,(owners F Q).card*markWeight L Q t)=∑ i : Fin 7,first t i*cutPopulation F L sz i := by
  rw [owner_weight_sum,cut_population_sum]
  exact sum_congr rfl (fun c _ => color_first F c L sz t)

theorem conditional_bounds (F : Factor V C) (a : C) (L : Finset V) (sz : L.card=12)
    (closed : Closed (F.f a) L) (t : Fin 3) :
    lowMean t≤conditionalMean F L t ∧ conditionalMean F L t≤highMean t := by
  have envelope := population_mean_bounds (cut_population_valid F L sz a closed) t
  rw [←labeled_mean] at envelope
  have lower : (∑ Q∈marks F univ,(owners F Q).card*markWeight L Q t)≤5*conditionalMean F L t := by
    rw [conditionalMean,mul_sum]
    apply sum_le_sum
    intro Q h
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast (owners_bounds F h).2) (weight_nonneg _ _ _)
  have upper : conditionalMean F L t≤∑ Q∈marks F univ,(owners F Q).card*markWeight L Q t := by
    apply sum_le_sum
    intro Q h
    exact le_mul_of_one_le_left (weight_nonneg _ _ _) (by exact_mod_cast (owners_bounds F h).1)
  constructor <;> linarith [envelope.1,envelope.2]

theorem actual_conditional_mean (F : Factor V C) (L : Finset V) (sz : L.card=12) (t : Fin 3) :
    sideAvg L (fun D => ((sideHits F L D t).card : ℚ))=conditionalMean F L t := by
  classical
  have den : (sideWays : ℚ)≠0 := by decide
  apply (div_eq_iff den).mpr
  unfold localSum conditionalMean
  rw [sum_mul]
  calc
    _ = ∑ D∈localSeal univ L,∑ Q∈marks F univ,
        if (Q∩L).card=6-3*t.val ∧ D∈localSeal univ Q then (1 : ℚ) else 0 := by
        simp [sideHits]
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro Q h
      rw [←split_mark_weight L Q sz (mark_mem.mp h).2.1 t]
      by_cases ty : (Q∩L).card=6-3*t.val
      · simp [ty,filter_mem_eq_inter]
      · simp [ty]

end WildSieve.Thirty.Graph
