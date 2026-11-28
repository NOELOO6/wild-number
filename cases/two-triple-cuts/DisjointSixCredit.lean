import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace WildSieve.TwoTripleCuts
open Finset

private theorem row (k h N : ℕ) (small : h<N) :
    ((2*k+1)*h)*N ≤ (k+1)*(k+2)*(N-1)+h*(h-1)*N := by
  have positive : 0<N := by omega
  by_cases zero : h=0
  · simp [zero]
  have H : (0:ℤ)≤h := by exact_mod_cast Nat.zero_le h
  have D : (0:ℤ)≤(N:ℤ)-h-1 := by omega
  have sign : (0:ℤ)≤((h:ℤ)-k)*((h:ℤ)-k-1) := by
    by_cases low : h≤k
    · apply mul_nonneg_of_nonpos_of_nonpos <;> omega
    · apply mul_nonneg <;> omega
  have rest : (0:ℤ)≤((h:ℤ)-k-1)^2+k+1 := by
    have := sq_nonneg ((h:ℤ)-k-1)
    omega
  have total := add_nonneg (mul_nonneg H sign) (mul_nonneg D rest)
  have id : ((k:ℤ)+1)*(k+2)*((N:ℤ)-1)+(h:ℤ)*(h-1)*N-(2*k+1)*(h:ℤ)*N =
      (h:ℤ)*(((h:ℤ)-k)*((h:ℤ)-k-1))+((N:ℤ)-h-1)*(((h:ℤ)-k-1)^2+k+1) := by ring
  have bound : (2*(k:ℤ)+1)*h*N≤(k+1)*(k+2)*((N:ℤ)-1)+(h:ℤ)*(h-1)*N := by
    linarith only [id,total]
  have hn : 1≤h := by omega
  have nn : 1≤N := by omega
  exact_mod_cast (by simpa only [Nat.cast_sub hn,Nat.cast_sub nn,Nat.cast_one] using bound :
    (2*(k:ℤ)+1)*h*N≤(k+1)*(k+2)*((N-1:Nat):ℤ)+(h:ℤ)*((h-1:Nat):ℤ)*N)

/-- Credit for simultaneous events in a layout. The selected neighbors may be any
subset of the other events, for instance the ones on disjoint six-sets. -/
theorem overlap_credit {α : Type*} (S : Finset α) (h : α → Nat) (k : Nat)
    (neighbours : ∀ i∈S,h i<S.card) :
    (2*k+1)*(∑ i∈S,h i) ≤ (k+1)*(k+2)*(S.card-1)+∑ i∈S,h i*(h i-1) := by
  classical
  by_cases empty : S=∅
  · simp [empty]
  have positive := card_pos.mpr (nonempty_iff_ne_empty.mpr empty)
  have s := sum_le_sum (fun i hi => row k (h i) S.card (neighbours i hi))
  rw [←sum_mul,←mul_sum,sum_add_distrib,sum_const,nsmul_eq_mul,←sum_mul] at s
  simp only [Nat.cast_id] at s
  rw [Nat.mul_comm S.card] at s
  rw [←Nat.add_mul] at s
  exact Nat.le_of_mul_le_mul_right s positive

#print axioms overlap_credit
end WildSieve.TwoTripleCuts
