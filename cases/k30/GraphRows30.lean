import RowSums30

namespace WildSieve.Thirty.Graph
open Finset
local instance (priority := 2000) graphRowsEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq
set_option maxRecDepth 12000

private theorem local_eq (F : Factor V C) (r : Row) (b : ℚ)
    (h : ∀ a L,L.card=12 → Closed (F.f a) L → atCut F L (coeff r)=b)
    (out : outside F (coeff r)=0) : graphEval F (coeff r)=b := by
  unfold graphEval
  rw [out,add_zero,cut_congr F _ (fun _ => b) (fun a L ha => h a L (anchor_valid ha).1 (anchor_valid ha).2),cut_const]

private theorem local_le (F : Factor V C) (r : Row) (b : ℚ)
    (h : ∀ a L,L.card=12 → Closed (F.f a) L → atCut F L (coeff r)≤b)
    (out : outside F (coeff r)=0) : graphEval F (coeff r)≤b := by
  unfold graphEval
  rw [out,add_zero,←cut_const F b]
  exact cut_mono F _ _ (fun a L ha => h a L (anchor_valid ha).1 (anchor_valid ha).2)

private theorem local_ge (F : Factor V C) (r : Row) (b : ℚ)
    (h : ∀ a L,L.card=12 → Closed (F.f a) L → b≤atCut F L (coeff r))
    (out : outside F (coeff r)=0) : b≤graphEval F (coeff r) := by
  unfold graphEval
  rw [out,add_zero,←cut_const F b]
  exact cut_mono F _ _ (fun a L ha => h a L (anchor_valid ha).1 (anchor_valid ha).2)

private theorem dup_colors (F : Factor V C) : graphEval F (coeff .duplicateColors)=0 := by
  have count : (∑ i : Fin 4,(duplicatePopulation F i : ℚ))=29*(defect F : ℚ) := by exact_mod_cast (duplicate_totals F).1
  simp [graphEval,atCut,histCol,outside,coeff,count]

private theorem dup_edges (F : Factor V C) : graphEval F (coeff .duplicateEdges)=0 := by
  have count : (∑ i : Fin 4,(i.val : ℚ)*(duplicatePopulation F i : ℚ))=15*(defect F : ℚ) := by exact_mod_cast (duplicate_totals F).2.1
  simp [graphEval,atCut,histCol,outside,coeff,count]

private theorem dup_closing (F : Factor V C) : 0≤graphEval F (coeff .duplicateClosing) := by
  have count : 2*(defect F : ℚ)≤(duplicatePopulation F 3 : ℚ) := by exact_mod_cast (duplicate_totals F).2.2
  have eq (i : Fin 4) : i.val=3 ↔ i=(3 : Fin 4) := ⟨fun h => Fin.ext h,fun h => h ▸ rfl⟩
  simp [graphEval,atCut,histCol,outside,coeff,eq,ite_mul]
  linarith

private theorem distinct_global (F : Factor V C) (t : Fin 3) : graphEval F (coeff (.distinct t))=0 := by
  have eq := cut_congr F (fun L => atCut F L (coeff (.distinct t))) (fun L => -duplicateMean F L t)
    (fun _ L h => distinct_row F L (anchor_valid h).1 t)
  have neg := cut_linear F (-1) (fun L => duplicateMean F L t) (fun _ => 0)
  simp only [neg_one_mul,add_zero,cut_const] at neg
  rw [graphEval,eq,neg,duplicate_average]
  simp only [outside,coeff,zero_mul,zero_add]
  simp only [div_eq_mul_inv,mul_right_comm _ (29 : ℚ)⁻¹,←sum_mul]
  ring

private theorem product_constraints (F : Factor V C) (L : Finset V) (l : L.card=12) (a : C) (cl : Closed (F.f a) L)
    (t : Fin 3) (i : Fin 7) (k : Fin 4) :
    let v := atCut F L (coeff (.product t i k))
    let b := -(cornerX i k)*cornerM t k
    if k.val<2 then b≤v else v≤b := by
  have x := population_bounds (cut_population_valid F L l a cl) i
  rw [←pop_eq F L l i] at x
  have y := conditional_bounds F a L l cl t
  have h := product_bounds _ _ _ _ _ _ x.1 x.2 y.1 y.2
  dsimp only
  rw [product_row_value F L l t i k]
  have four : ∀ j : Fin 4,j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by decide
  rcases four k with rfl|rfl|rfl|rfl <;> norm_num [show (3 : Fin 4).val=3 by decide,cornerX,cornerM,Fin.reduceFinMk] <;>
    linarith only [h.1,h.2.1,h.2.2.1,h.2.2.2]

private theorem product_global (F : Factor V C) (t : Fin 3) (i : Fin 7) (k : Fin 4) :
    RowHolds (graphEval F) (.product t i k) := by
  unfold RowHolds sense rhs
  by_cases low : k.val<2
  · simp only [low,if_true]
    apply local_ge
    · intro a L l cl
      simpa only [low,if_true] using product_constraints F L l a cl t i k
    · simp [outside,coeff]
  · simp only [low,if_false]
    apply local_le
    · intro a L l cl
      simpa only [low,if_false] using product_constraints F L l a cl t i k
    · simp [outside,coeff]

/-- Every row used by the rational certificate holds for the distribution
constructed from an arbitrary minimum proper coloring. -/
theorem graph_rows (F : Factor V C) (r : Row) (h : indexed r=true) : RowHolds (graphEval F) r := by
  cases r with
  | mass => exact local_eq F _ _ (fun _ L l _ => mass_row F L l) (by simp [outside,coeff])
  | colors => exact local_eq F _ _ (fun a L l cl => colors_row F L l a cl) (by simp [outside,coeff])
  | leftEdges => exact local_eq F _ _ (fun a L l cl => edges_row F L l a cl) (by simp [outside,coeff])
  | anchorColor => exact local_ge F _ _ (fun a L l cl => anchor_row F L l a cl) (by simp [outside,coeff])
  | duplicateColors => exact dup_colors F
  | duplicateEdges => exact dup_edges F
  | duplicateClosing => exact dup_closing F
  | mean t =>
    exact local_eq F _ _ (fun _ L l _ => mean_row F L l ⟨t,by simpa [indexed] using h⟩) (by simp [outside,coeff])
  | distinct t => exact distinct_global F ⟨t,by simpa [indexed] using h⟩
  | regionalColors t =>
    exact local_eq F _ _ (fun _ L l _ => regional_row F L l ⟨t,by simpa [indexed] using h⟩) (by simp [outside,coeff])
  | edges t k =>
    simp [indexed] at h
    exact local_eq F _ _ (fun _ L l _ => cell_row F L l ⟨t,h.1⟩ ⟨k,h.2⟩) (by simp [outside,coeff])
  | anchor t =>
    exact local_ge F _ _ (fun a L l cl => anchor_signature_row F L l a cl ⟨t,by simpa [indexed] using h⟩) (by simp [outside,coeff])
  | closing t i =>
    simp [indexed] at h
    exact local_eq F _ _ (fun _ L l _ => closing_row F L l ⟨t,h.1⟩ ⟨i,h.2⟩) (by simp [outside,coeff])
  | product t i k =>
    simp [indexed] at h
    exact product_global F ⟨t,h.1.1⟩ ⟨i,h.1.2⟩ ⟨k,h.2⟩
  | other t k =>
    simp [indexed] at h
    exact local_le F _ _ (fun _ L l _ => other_row F L l ⟨t,h.1⟩ ⟨k,h.2⟩) (by simp [outside,coeff])
  | complement => exact local_le F _ _ (fun _ L l _ => complement_row F L l) (by simp [outside,coeff])

end WildSieve.Thirty.Graph
