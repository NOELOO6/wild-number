import FrameColors30

namespace WildSieve.Thirty.Graph
open Finset
local instance (priority := 2000) otherEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq
set_option maxRecDepth 12000

noncomputable def otherCount (L : Finset V) (P : Pattern) (k : Fin 3) (Q : Finset V) : Nat :=
  if Q≠vertices P ∧ (Q∩L).card=6-3*k.val then (frameEvent L P∩localSeal univ Q).card else 0

theorem other_at_frame (F : Factor V C) (L : Finset V) (P : Pattern) (k : Fin 3) :
    (∑ D∈frameEvent L P,((sideHits F L D k).erase (vertices P)).card)=∑ Q∈marks F univ,otherCount L P k Q := by
  classical
  have per (D : Deck) : ((sideHits F L D k).erase (vertices P)).card =
      ∑ Q∈marks F univ,if (Q≠vertices P ∧ (Q∩L).card=6-3*k.val) ∧ D∈localSeal univ Q then 1 else 0 := by
    rw [sum_boole]
    congr 1
    ext Q
    simp only [mem_erase,sideHits,mem_filter]
    tauto
  simp_rw [per]
  rw [sum_comm]
  apply sum_congr rfl
  intro Q _
  by_cases h : Q≠vertices P ∧ (Q∩L).card=6-3*k.val
  · simp [otherCount,h,filter_mem_eq_inter]
  · simp [otherCount,h]

theorem other_labeled (F : Factor V C) (L : Finset V) (l : L.card=12) (t k : Fin 3) (P : Pattern)
    (hp : P∈frames F L t) :
    (∑ Q∈marks F univ,(owners F Q).card*(otherCount L P k Q : ℚ))=
      (frameEvent L P).card*∑ c,otherBill t k (signatureOf F c (regionOf F L t P)) := by
  let z := regionOf F L t P
  have spec := region_spec F L l t P hp
  have size := frame_size z t spec.sizes
  rw [spec.decks] at size
  rw [owner_weight_sum,mul_sum]
  apply sum_congr rfl
  intro c _
  have law := other_completions_sum F c z t k spec.sizes
  rw [Nat.cast_sum,←size,mul_comm] at law
  refine Eq.trans (sum_congr rfl (fun Q h => ?_)) law
  have eq := frame_other_weight Q (candidate_mem.mp h).2.1 z t k spec.sizes
  rw [spec.mark,spec.left,spec.decks] at eq
  exact_mod_cast eq

theorem other_distinct_le (F : Factor V C) (L : Finset V) (P : Pattern) (k : Fin 3) :
    (∑ Q∈marks F univ,(otherCount L P k Q : ℚ))≤∑ Q∈marks F univ,(owners F Q).card*(otherCount L P k Q : ℚ) := by
  apply sum_le_sum
  intro Q h
  exact le_mul_of_one_le_left (Nat.cast_nonneg _) (by exact_mod_cast (owners_bounds F h).1)

private theorem single_free (F : Factor V C) (L : Finset V) (l : L.card=12) (P : Pattern) (hp : P∈frames F L 0) :
    let z := regionOf F L 0 P
    let U := zone z 2
    U.card=6 ∧ otherCount L P 0 U=(frameEvent L P).card := by
  let z := regionOf F L 0 P
  let U := zone z 2
  have spec := region_spec F L l 0 P hp
  have sz : U.card=6 := spec.sizes 2
  have left : U⊆L := by
    rw [←spec.left]
    intro v hv
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    change leftMask 0 (z v)=true
    rw [show z v=2 from (mem_filter.mp hv).2]
    decide
  have dis : Disjoint U (vertices P) := by
    rw [←spec.mark]
    apply disjoint_left.mpr
    intro v hv hm
    have hy := (mem_filter.mp hm).2
    change hitMask (z v)=true at hy
    rw [show z v=2 from (mem_filter.mp hv).2] at hy
    contradiction
  have ne : U≠vertices P := by
    intro same
    have empty := disjoint_self.mp (same.symm ▸ dis)
    change U=∅ at empty
    rw [empty,card_empty] at sz
    omega
  have all : frameEvent L P⊆localSeal univ U := by
    rw [←spec.decks]
    exact fun _ h => Regions.decks_mem.mp h 2
  refine ⟨sz,?_⟩
  change otherCount L P 0 U=_
  unfold otherCount
  rw [if_pos ⟨ne,by rw [inter_eq_left.mpr left,sz]; decide⟩,inter_eq_left.mpr all]

def complementCharge (s : Signature) : ℚ := if s.c+s.g+s.y=0 then 1 else 0

theorem other_complement_le (F : Factor V C) (L : Finset V) (l : L.card=12) (P : Pattern) (hp : P∈frames F L 0) :
    let z := regionOf F L 0 P
    (∑ Q∈marks F univ,(otherCount L P 0 Q : ℚ))+(frameEvent L P).card*∑ c,complementCharge (signatureOf F c z)
      ≤ (frameEvent L P).card*(∑ c,otherBill 0 0 (signatureOf F c z))+(frameEvent L P).card := by
  let z := regionOf F L 0 P
  let U := zone z 2
  obtain ⟨sz,single⟩ := single_free F L l P hp
  have coord : selected z freeLeft=U := by ext v; simp [U,zone,selected,freeLeft]
  have ch (c : C) : complementCharge (signatureOf F c z)=(if c∈owners F U then 1 else 0 : ℚ) := by
    unfold complementCharge
    have iff := complement_flag F c z
    rw [coord,←owner_mem] at iff
    by_cases h : c∈owners F U
    · rw [if_pos h,if_pos (iff.mp h)]
    · rw [if_neg h,if_neg (fun eq => h (iff.mpr eq))]
  change _+(frameEvent L P).card*(∑ c,complementCharge (signatureOf F c z))≤_
  simp_rw [ch]
  simp only [sum_boole,filter_mem_eq_inter,univ_inter]
  have row := other_labeled F L l 0 0 P hp
  change _=(frameEvent L P).card*∑ c,otherBill 0 0 (signatureOf F c z) at row
  rw [←row]
  by_cases yes : U∈marks F univ
  · rw [←sum_erase_add _ _ yes,←sum_erase_add _ (fun Q => (owners F Q).card*(otherCount L P 0 Q : ℚ)) yes]
    have rest := sum_le_sum (s:=(marks F univ).erase U) (fun Q h => le_mul_of_one_le_left
      (Nat.cast_nonneg (otherCount L P 0 Q) : (0 : ℚ)≤_) (show (1 : ℚ)≤(owners F Q).card by exact_mod_cast (owners_bounds F (mem_erase.mp h).2).1))
    change otherCount L P 0 U=(frameEvent L P).card at single
    rw [single]
    linarith
  · have empty : owners F U=∅ := by
      apply eq_empty_iff_forall_not_mem.mpr
      intro c hc
      exact yes (mark_mem.mpr ⟨subset_univ _,sz,c,owner_mem.mp hc⟩)
    simp only [empty,card_empty,Nat.cast_zero,mul_zero,add_zero]
    exact (other_distinct_le F L P 0).trans (le_add_of_nonneg_right (Nat.cast_nonneg _))

end WildSieve.Thirty.Graph
