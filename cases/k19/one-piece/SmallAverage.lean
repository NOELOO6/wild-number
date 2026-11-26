import GroupMerges
namespace WildPieces
open Finset
theorem aggregate {P : Type} [Fintype P] (w a b c : P → Nat)
    (each : ∀ p, w p+b p ≤ a p+2*c p) (ha : ∑ p, a p = 13218228559872000)
    (hb : ∑ p, b p = 468787544064000) (hc : ∑ p, c p = 5643509760000) :
    19 * (∑ p, w p) < 243290200817664000 := by
  have h := Finset.sum_le_sum (s:=univ) (fun p _ => each p)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,ha,hb,hc] at h
  omega

theorem pivot {P C : Type} [Fintype P] [Fintype C] (f : C → P → Nat) (s : Nat)
    (hs : ∀ c, ∑ p, f c p = s) (bound : Fintype.card C * s < Fintype.card P * 2) :
    ∃ p, (∑ c, f c p) ≤ 1 := by
  have less : (∑ p, ∑ c, f c p) < ∑ _p : P, 2 := by
    rw [Finset.sum_comm]
    simpa only [hs,Finset.sum_const,Finset.card_univ,smul_eq_mul] using bound
  obtain ⟨p,_,h⟩ := Finset.exists_lt_of_sum_lt less
  exact ⟨p,Nat.le_of_lt_succ h⟩
end WildPieces
