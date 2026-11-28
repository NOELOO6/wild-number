import BalancedSampling24
import Motifs24
import PatternGeometry
import RestrictedNeighbors

namespace WildSieve.TwentyFour
open Finset EvenTriples WildExact SixCounts EdgeDeletion
set_option maxRecDepth 9000
set_option maxHeartbeats 1600000
local instance (priority := 2000) shortEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq

/-- Actual edges on a triple partition: each is a pair whose union is closed in some color. -/
noncomputable def hits (F : Factor V C) (D : Deck) := (family F).filter (·⊆D.val)

private theorem nonempty_hits (F : Factor V C) (D : Deck) :
    (hits F D).Nonempty ↔ D∉noSix F univ := by
  rw [←mem_compl,←event_pattern_union]
  simp only [hits,filter_nonempty_iff,mem_biUnion,event,extensions,mem_filter,mem_univ,true_and]

private theorem edge_sum (F : Factor V C) :
    (∑ D : Deck,(hits F D).card)=10*(marks F univ).card*ways 6 := by
  classical
  simp only [hits,Finset.card_filter]
  rw [sum_comm]
  have each (P) (h : P∈family F) :
      (∑ D : Deck,if P⊆D.val then 1 else 0)=ways 6 := by
    have base := event_mass 8 (by decide : 24=3*8) (pattern_mem.mp h).1
    rw [pattern_size h] at base
    change ((univ : Finset Deck).filter (fun D => P⊆D.val)).card=_ at base
    simpa only [Finset.card_filter] using base
  rw [sum_congr rfl each,sum_const,nsmul_eq_mul]
  simp only [family,pattern_card,Nat.cast_id]

/-- The eight-block motif inequality summed over the partitions of the actual coloring. -/
theorem short_motifs (F : Factor V C) :
    42*((noSix F univ)ᶜ).card + (∑ D : Deck,bill Motifs.pairCost 2 (hits F D)) ≤
      42*(10*(marks F univ).card*ways 6) + ∑ D : Deck,bill Motifs.tripleCredit 3 (hits F D) := by
  classical
  have per (D : Deck) : 42*(if D∉noSix F univ then 1 else 0)+bill Motifs.pairCost 2 (hits F D)≤
       42*(hits F D).card+bill Motifs.tripleCredit 3 (hits F D) := by
    have len := D.property.1.card_vertices
    rw [D.property.2,card_univ,Fintype.card_fin] at len
    have yes := of_decide_eq_true (Motifs.graph_on_blocks D.val (by omega) (hits F D)
      (fun _ h => pattern_size (mem_filter.mp h).1) (fun _ h => (mem_filter.mp h).2))
    by_cases bad : D∉noSix F univ
    · simp only [if_pos bad,Nat.mul_one]
      exact yes.resolve_left (Nat.ne_of_gt (card_pos.mpr ((nonempty_hits F D).mpr bad)))
    · have nil := not_nonempty_iff_eq_empty.mp (fun h => bad ((nonempty_hits F D).mp h))
      simp [nil,bad,bill,Finset.powersetCard_eq_empty.mpr]
  have all := sum_le_sum (s:=univ) (fun D _ => per D)
  simp only [sum_add_distrib,←mul_sum,edge_sum] at all
  have cnt : (∑ D : Deck,if D∉noSix F univ then 1 else 0)=((noSix F univ)ᶜ).card := by
    rw [←Finset.card_filter]
    congr 1
    ext
    simp
  rwa [cnt] at all

theorem complement_caps (F : Factor V C) (U : Finset V) :
    (U.card=12 → labeled F U≤220) ∧ (U.card=15 → labeled F U≤329) ∧
    (U.card=18 → labeled F U≤780) := by
  refine ⟨fun h => ?_,fun h => ?_,fun h => ?_⟩
  · have a := chord F U 12 6 0 20 h (by decide)
    change 6*labeled F U+0≤1320 at a
    omega
  · have a := chord F U 15 4 98 34 h (by decide)
    change 4*labeled F U+2254≤3570 at a
    omega
  · have a := chord F U 18 3 324 64 h (by decide)
    change 3*labeled F U+7452≤9792 at a
    omega

theorem wedge_extensions (F : Factor V C) (A U : Finset V) (a : A.card=3) (u : U.card=15) :
    ((neighbors F A).filter (fun B => B⊆U)).card≤36 := by
  simpa only [u] using restricted_neighbors F A U a

/-- A shorter end-to-end argument applies when at least 1,410 six-set labels are surplus. -/
theorem exact_of_duplicates (g : Coloring 24 23) (many : 1410≤defect (coloringFactor g)) : Exact g 16 := by
  classical
  let F : Factor V C := coloringFactor g
  have short : ((noSix F univ)ᶜ).card≤10*(marks F univ).card*ways 6 := by
    rw [←edge_sum]
    calc
      _ = ∑ D∈(noSix F univ)ᶜ,1 := by simp
      _ ≤ ∑ D∈(noSix F univ)ᶜ,(hits F D).card := sum_le_sum (fun D h =>
        card_pos.mpr ((nonempty_hits F D).mpr (mem_compl.mp h)))
      _ ≤ _ := sum_le_sum_of_subset (subset_univ _)
  have per (S : Finset V) (h : S∈cuts F (Fin.last 23) 8 4) :
      (survivingSide F S).card≤14400*14400 := by
    obtain ⟨c,hc⟩ := side_mem.mp h
    obtain ⟨_,sz,cl⟩ := candidate_mem.mp hc
    exact long_noSix F S c (by simpa using cl) 4 4 sz
      (by rw [card_compl,Fintype.card_fin,sz]) (by decide) (by decide)
  have late := card_biUnion_le.trans (sum_le_sum per)
  rw [sum_const,nsmul_eq_mul] at late
  have num := pure_global F (Fin.last 23) 8 4 24 (by simp) (by simp)
  have cap : (lateBad F).card≤pureTotal 24 8 4*(14400*14400) :=
    late.trans (Nat.mul_le_mul_right _ num)
  change (lateBad F).card≤2203407360000 at cap
  have h := (full_defect F).2
  change (marks F univ).card+defect F=5060 at h
  change 1410≤defect F at many
  change _≤10*(marks F univ).card*190590400 at short
  have full := card_compl (noSix F univ)
  rw [card_layout 8 univ (by decide : (univ : Finset V).card=3*8)] at full
  change _=9161680528000-_ at full
  have bound : (lateBad F).card < (noSix F univ).card := by omega
  have missing : ¬noSix F univ ⊆ lateBad F := fun sub => (Nat.not_le_of_gt bound) (card_le_card sub)
  obtain ⟨D,hd,none⟩ := not_subset.mp missing
  exact exact_of_survivor g D hd none

#print axioms short_motifs
#print axioms exact_of_duplicates
end WildSieve.TwentyFour
