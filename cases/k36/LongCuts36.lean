import Region24

namespace WildSieve.ThirtySix
open Finset EvenTriples
local instance (priority := 2000) longVertexEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq

def cap24 (d : Nat) := min (ways 8-saving false 12 8)
  ((6*ways 8+d*regionalCredit-1956*regionalCredit)/6)

private theorem cap24_valid (F : Factor V C) (X : Finset V) (size : X.card=24)
    (c : C) (cl : Closed (F.f c) X) : (noSix F X).card≤cap24 (defect F) := by
  apply Nat.le_min.mpr
  refine ⟨inside_noSix F X c cl 8 size (by decide),?_⟩
  have credit := region_credit F X size c cl
  omega

noncomputable def losses (F : Factor V C) (j : Nat) :=
  (cuts F (Fin.last 35) 12 j).biUnion (fun S => noSix F univ∩localSeal univ S)

def price4 (d : Nat) := pureTotal 36 12 4 * ((ways 4-saving false 6 4)*cap24 d)
def price6 := pureTotal 36 12 6 * ((ways 6-saving false 9 6)*(ways 6-saving false 9 6))

private theorem late_bound (F : Factor V C) (j cost : Nat)
    (unit : ∀ S∈cuts F (Fin.last 35) 12 j,(noSix F univ∩localSeal univ S).card≤cost) :
    (losses F j).card≤pureTotal 36 12 j*cost := by
  classical
  have total := card_biUnion_le.trans (sum_le_sum unit)
  rw [sum_const,nsmul_eq_mul] at total
  have high := pure_global F (Fin.last 35) 12 j 36 (by simp) (by simp)
  exact total.trans (Nat.mul_le_mul_right cost high)

theorem late_four (F : Factor V C) : (losses F 4).card≤price4 (defect F) := by
  apply late_bound
  intro S h
  obtain ⟨c,hc⟩ := side_mem.mp h
  obtain ⟨_,sz,closed⟩ := candidate_mem.mp hc
  have cl : Closed (F.f c) S := by simpa using closed
  have other : Sᶜ.card=24 := by rw [card_compl,Fintype.card_fin,sz]
  exact (noSix_product F S).trans (Nat.mul_le_mul (inside_noSix F S c cl 4 sz (by decide))
    (cap24_valid F Sᶜ other c (closed_complement F c S cl)))

theorem late_six (F : Factor V C) : (losses F 6).card≤price6 := by
  apply late_bound
  intro S h
  obtain ⟨c,hc⟩ := side_mem.mp h
  obtain ⟨_,sz,closed⟩ := candidate_mem.mp hc
  exact long_noSix F S c (by simpa using closed) 6 6 sz
    (by rw [card_compl,Fintype.card_fin,sz]) (by decide) (by decide)

end WildSieve.ThirtySix
