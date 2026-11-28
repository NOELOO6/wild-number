import SignatureMeans30

namespace WildSieve.Thirty.Graph
open Finset
local instance (priority := 2000) functionalEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq
set_option maxRecDepth 12000

noncomputable def histCol (F : Factor V C) (L : Finset V) (D : Deck) : Column :=
  .hist (sideHits F L D 0).card (sideHits F L D 1).card (sideHits F L D 2).card

noncomputable def atCut (F : Factor V C) (L : Finset V) (w : Column → ℚ) :=
  sideAvg L (fun D => w (histCol F L D)) +
  (∑ i : Fin 7,w (.colors i)*pop F L i) +
  (∑ t : Fin 3,w (.mean t)*conditionalMean F L t) +
  ∑ t : Fin 3,sigMean F L t (fun s => w (.signature t s))

noncomputable def outside (F : Factor V C) (w : Column → ℚ) :=
  w .defect*(defect F : ℚ)+∑ i : Fin 4,w (.duplicates i)*(duplicatePopulation F i : ℚ)

noncomputable def graphEval (F : Factor V C) (w : Column → ℚ) := cutAvg F (fun L => atCut F L w)+outside F w

private theorem simple_columns : (∀ i : Fin 7,Column.colors i∈columns) ∧
    (∀ i : Fin 4,Column.duplicates i∈columns) ∧ (∀ t : Fin 3,Column.mean t∈columns) ∧
    Column.defect∈columns := by native_decide

private theorem sig_col (t : Fin 3) (s : Signature) (h : s∈signatures t) : Column.signature t s∈columns :=
  List.mem_append_right _ (List.mem_flatMap.mpr ⟨t.val,List.mem_range.mpr t.isLt,List.mem_map.mpr ⟨s,h,rfl⟩⟩)

theorem eval_dominates (F : Factor V C) : graphEval F objective≤graphEval F priced := by
  have facts := simple_columns
  unfold graphEval
  apply add_le_add
  · apply cut_mono
    intro a L hL
    have size := (anchor_valid hL).1
    unfold atCut
    apply add_le_add
    · apply add_le_add
      · apply add_le_add
        · exact side_mono L _ _ (fun D hd => dominates (histogram_column F L size D hd))
        · exact sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (dominates (facts.1 i)) (Nat.cast_nonneg _))
      · exact sum_le_sum (fun t _ => mul_le_mul_of_nonneg_right (dominates (facts.2.2.1 t)) (mean_nonneg F L t))
    · apply sum_le_sum
      intro t _
      apply frame_mono
      intro P hp
      apply sum_le_sum
      intro c _
      exact dominates (sig_col t _ (mem_signatures (signature_fits F c _ t (region_spec F L size t P hp).sizes)))
  · unfold outside
    exact add_le_add (mul_le_mul_of_nonneg_right (dominates facts.2.2.2) (Nat.cast_nonneg _))
      (sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (dominates (facts.2.1 i)) (Nat.cast_nonneg _)))

@[simp] theorem eval_zero (F : Factor V C) : graphEval F (fun _ => 0)=0 := by
  simp [graphEval,atCut,outside]

theorem eval_linear (F : Factor V C) (a : ℚ) (f g : Column → ℚ) :
    graphEval F (fun j => a*f j+g j)=a*graphEval F f+graphEval F g := by
  have each (L : Finset V) : atCut F L (fun j => a*f j+g j)=a*atCut F L f+atCut F L g := by
    unfold atCut
    simp only [side_linear,sig_linear,add_mul,mul_assoc,sum_add_distrib,←mul_sum]
    ring
  simp only [graphEval,each,cut_linear,outside,add_mul,mul_assoc,sum_add_distrib,←mul_sum]
  ring

private theorem chance_zero (F : Factor V C) (L : Finset V) :
    sideAvg L (fun D => objective (histCol F L D))=((noSix F univ∩localSeal univ L).card : ℚ)/sideWays := by
  classical
  unfold sideAvg localSum
  congr 1
  have per (D : Deck) (h : D∈localSeal univ L) : objective (histCol F L D)=
      if D∈noSix F univ then 1 else 0 := by
    have menu : ∀ t : Fin 3,t=0 ∨ t=1 ∨ t=2 := by decide
    have iff : D∈noSix F univ ↔ (sideHits F L D 0).card=0 ∧ (sideHits F L D 1).card=0 ∧ (sideHits F L D 2).card=0 := by
      rw [←sample_zero F L D h]
      simp only [card_eq_zero]
      exact ⟨fun yes => ⟨yes 0,yes 1,yes 2⟩,fun ⟨a,b,c⟩ t => by rcases menu t with rfl|rfl|rfl <;> assumption⟩
    simp only [histCol,iff]
    rcases (sideHits F L D 0).card with _|a <;> rcases (sideHits F L D 1).card with _|b <;>
      rcases (sideHits F L D 2).card with _|c <;> simp [objective]
  rw [sum_congr rfl per,sum_boole,filter_mem_eq_inter,inter_comm]

theorem eval_objective (F : Factor V C) : graphEval F objective=noHitChance F-(defect F : ℚ)/18000 := by
  have each (L : Finset V) : atCut F L objective=((noSix F univ∩localSeal univ L).card : ℚ)/sideWays := by
    unfold atCut
    rw [chance_zero]
    simp [objective]
  simp only [graphEval,each,outside,objective,zero_mul,sum_const_zero,add_zero,noHitChance]
  ring

end WildSieve.Thirty.Graph
