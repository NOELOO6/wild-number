import GraphFunctional30

namespace WildSieve.Thirty.Graph
open Finset
local instance (priority := 2000) sumsEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq
set_option maxRecDepth 12000

theorem index_sum {n : Nat} (v : Fin n) (b : ℚ) (w : Fin n → ℚ) :
    (∑ j : Fin n,(if v.val=j.val then b else 0)*w j)=b*w v := by
  classical
  have eq (j : Fin n) : v.val=j.val ↔ j=v := ⟨fun h => Fin.ext h.symm,fun h => h ▸ rfl⟩
  simp [eq,ite_mul]

theorem sig_index (F : Factor V C) (L : Finset V) (t : Fin 3) (w : Signature → ℚ) :
    (∑ j : Fin 3,sigMean F L j (fun s => if t.val=j.val then w s else 0))=sigMean F L t w := by
  rw [sum_eq_single t]
  · simp
  · intro j _ ne
    have ij : t.val≠j.val := fun h => ne (Fin.ext h.symm)
    simp [ij]
  · simp

private theorem pick_hits (F : Factor V C) (L : Finset V) (D : Deck) (t : Fin 3) :
    pick (sideHits F L D 0).card (sideHits F L D 1).card (sideHits F L D 2).card t=(sideHits F L D t).card := by
  have menu : ∀ i : Fin 3,i=0 ∨ i=1 ∨ i=2 := by decide
  rcases menu t with rfl|rfl|rfl <;> rfl

theorem mass_row (F : Factor V C) (L : Finset V) (l : L.card=12) : atCut F L (coeff .mass)=1 := by
  simp [atCut,histCol,coeff,side_const L l]

theorem colors_row (F : Factor V C) (L : Finset V) (l : L.card=12) (a : C) (cl : Closed (F.f a) L) :
    atCut F L (coeff .colors)=29 := by
  simpa [atCut,histCol,coeff,pop_eq F L l] using (cut_population_valid F L l a cl).colors

theorem edges_row (F : Factor V C) (L : Finset V) (l : L.card=12) (a : C) (cl : Closed (F.f a) L) :
    atCut F L (coeff .leftEdges)=66 := by
  simpa [atCut,histCol,coeff,pop_eq F L l] using (cut_population_valid F L l a cl).edges

theorem anchor_row (F : Factor V C) (L : Finset V) (l : L.card=12) (a : C) (cl : Closed (F.f a) L) :
    1≤atCut F L (coeff .anchorColor) := by
  have eq (i : Fin 7) : i.val=6 ↔ i=(6 : Fin 7) := ⟨fun h => Fin.ext h,fun h => h ▸ rfl⟩
  simpa [atCut,histCol,coeff,eq,ite_mul,pop_eq F L l] using (cut_population_valid F L l a cl).anchor

theorem mean_row (F : Factor V C) (L : Finset V) (l : L.card=12) (t : Fin 3) :
    atCut F L (coeff (.mean t))=0 := by
  simp only [atCut,histCol,coeff,pick_hits,zero_mul,sum_const_zero,sig_zero,add_zero,
    index_sum,neg_one_mul,actual_conditional_mean F L l t,add_neg_cancel]

theorem distinct_row (F : Factor V C) (L : Finset V) (l : L.card=12) (t : Fin 3) :
    atCut F L (coeff (.distinct t))= -duplicateMean F L t := by
  have h := distinct_at_cut F L l t
  simp only [atCut,histCol,coeff,side_zero,sig_zero,neg_mul,sum_neg_distrib,index_sum,one_mul,
    sum_const_zero,zero_add,add_zero,pop_eq F L l]
  linarith

theorem regional_row (F : Factor V C) (L : Finset V) (l : L.card=12) (t : Fin 3) :
    atCut F L (coeff (.regionalColors t))=0 := by
  simp only [atCut,histCol,coeff,side_zero,zero_mul,sum_const_zero,zero_add,index_sum,sig_index,sig_mass F L l]
  ring

theorem cell_row (F : Factor V C) (L : Finset V) (l : L.card=12) (t : Fin 3) (k : Fin 10) :
    atCut F L (coeff (.edges t k))=0 := by
  simp only [atCut,histCol,coeff,side_zero,zero_mul,sum_const_zero,zero_add,index_sum,sig_index,sig_edges F L l]
  ring

theorem anchor_signature_row (F : Factor V C) (L : Finset V) (l : L.card=12) (a : C) (cl : Closed (F.f a) L)
    (t : Fin 3) : 0≤atCut F L (coeff (.anchor t)) := by
  simp only [atCut,histCol,coeff,side_zero,zero_mul,sum_const_zero,zero_add,index_sum,ite_and,sig_index,neg_one_mul]
  linarith only [sig_anchor F L l a cl t]

theorem closing_row (F : Factor V C) (L : Finset V) (l : L.card=12) (t : Fin 3) (i : Fin 7) :
    atCut F L (coeff (.closing t i))=0 := by
  simp only [atCut,histCol,coeff,side_zero,zero_mul,sum_const_zero,zero_add,add_zero,index_sum,ite_and,sig_index]
  have h := sig_closing F L l t i
  simp only [ite_and] at h
  rw [h]
  ring

theorem product_row_value (F : Factor V C) (L : Finset V) (l : L.card=12) (t : Fin 3) (i : Fin 7) (k : Fin 4) :
    atCut F L (coeff (.product t i k)) = pop F L i*conditionalMean F L t-
      cornerX i k*conditionalMean F L t-cornerM t k*pop F L i := by
  simp only [atCut,histCol,coeff,side_zero,zero_add,index_sum,ite_and,sig_index,sig_population F L l]
  ring

theorem other_row (F : Factor V C) (L : Finset V) (l : L.card=12) (t k : Fin 3) :
    atCut F L (coeff (.other t k))≤0 := by
  have tk : ((t : Nat)=k.val) ↔ t=k := Fin.ext_iff.symm
  simp only [atCut,histCol,coeff,otherMoment,pick_hits,tk,zero_mul,sum_const_zero,add_zero,sig_index]
  change secondMean F L t k+sigMean F L t (fun s => -otherBill t k s)≤0
  have h := sig_linear F L t (-1) (otherBill t k) (fun _ => 0)
  simp only [neg_one_mul,add_zero,sig_zero] at h
  rw [h]
  linarith only [sig_other F L l t k]

theorem complement_row (F : Factor V C) (L : Finset V) (l : L.card=12) :
    atCut F L (coeff .complement)≤0 := by
  have hm := index_sum (0 : Fin 3) (-1) (conditionalMean F L)
  have hs := sig_index F L 0 (fun s => complementCharge s-otherBill 0 0 s)
  simp only [Fin.val_zero,eq_comm (a:=0)] at hm hs
  simp only [atCut,histCol,coeff,zero_mul,sum_const_zero,add_zero,hm,neg_one_mul]
  change secondMean F L 0 0 + -conditionalMean F L 0 + _≤0
  unfold complementCharge at hs
  rw [hs]
  have cap := sig_complement F L l
  unfold complementCharge at cap
  linarith only [cap]

end WildSieve.Thirty.Graph
