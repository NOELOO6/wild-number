import EvenSeries
import EvenOrders
import ExactTrimmed
import Exact42

namespace WildSieve.EvenTriples
open Finset WildExact

/-- An integer version of the ordinary union bound for a partition into triples. -/
private def rawCount (n t j : Nat) := if (3*j)%2=0 then
  (n-1)*Nat.fast_choose (n/2-(if 2*j=t then 1 else 0)) (3*j/2) else 0
private def rawOK (m : Nat) := decide (
  (∑ j∈shortLevels∪longLevels (2*m),rawCount (6*m) (2*m) j*numerator (2*m) j)<ways (2*m))

set_option maxRecDepth 200000
set_option maxHeartbeats 0
private theorem middle_check : (List.range 56).all (fun i => rawOK (14+i))=true := by decide

private theorem middle_sum (m : Nat) (lo : 14≤m) (hi : m<70) :
    (∑ j∈shortLevels∪longLevels (2*m),(pureTotal (6*m) (2*m) j:ℚ)*sealWeight (2*m) j)<1 := by
  have ok := of_decide_eq_true (List.all_eq_true.mp middle_check (m-14)
    (List.mem_range.mpr (by omega)))
  rw [show 14+(m-14)=m by omega] at ok
  have scaled := weighted (2*m) (shortLevels∪longLevels (2*m)) (pureTotal (6*m) (2*m)) (fun _ => 1)
  simp only [Nat.cast_one,mul_one] at scaled
  rw [scaled,div_lt_iff₀ (show (0:ℚ)<ways (2*m) by exact_mod_cast ways_pos _),one_mul]
  exact_mod_cast (by simpa only [rawCount,←Nat.choose_eq_fast_choose,pureTotal] using ok :
    (∑ j∈shortLevels∪longLevels (2*m),pureTotal (6*m) (2*m) j*numerator (2*m) j)<ways (2*m))

local instance (priority := 2000) seriesFinEq {m : Nat} : DecidableEq (Fin m) :=
  (inferInstance : LinearOrder (Fin m)).toDecidableEq

private theorem exact_from_sum (n m : Nat) (lo : 3≤n+1) (size : n+1=6*m)
    (small : (∑ j∈shortLevels∪longLevels (2*m),(pureTotal (6*m) (2*m) j:ℚ)*sealWeight (2*m) j)<1)
    (g : Coloring (n+1) n) : Exact g (4*m) := by
  let F := coloringFactor g
  let r := Fin.last n
  let t := 2*m
  have pts : Fintype.card (Fin (n+1))=6*m := (Fintype.card_fin _).trans size
  have cols : Fintype.card (Fin n)=6*m-1 := by simp; omega
  have sz : n+1=3*t := by dsimp [t]; omega
  obtain ⟨L,_,pass⟩ := partition_split t ((Fintype.card_fin _).trans sz) ∅ (shortLevels∪longLevels t)
    (cuts F r t) (cuts F r t) (by simp) (fun j _ => cut_size F r t j) (by simp)
    (fun _ _ => 0) (pureTotal (6*m) t) (by simp) (fun j _ => pure_global F r t j _ pts cols)
    (fun _ => (1:ℚ)) (by simp) (by simp) (by simpa [t] using small)
  apply exact_of_upper (show Upper g (4*m) by simpa [t,←Nat.mul_assoc] using pure_upper g r t sz L pass)
  intro w le works
  have b := even_lower lo g le works
  omega

/-- For every m ≥ 7 and every minimum proper edge coloring of K_(6m),
exactly 4m wild edges are necessary and sufficient. -/
theorem exact_multiples_of_six (m : Nat) (lo : 7≤m) :
    ∀ g : Coloring (6*m) (6*m-1),Exact g (4*m) := by
  by_cases first : m=7
  · subst m
    exact FortyTwo.exact_K42
  by_cases high : 14≤m
  · have sum := if big : 70≤m then large_sum m big else middle_sum m high (by omega)
    generalize eq : 6*m=n at *
    cases n with
    | zero => omega
    | succ n => exact exact_from_sum n m (by omega) eq.symm (eq ▸ sum)
  by_cases edge : m=13
  · subst m
    exact exact_K77_K78.2
  have mem : 6*m∈[48,54,60,66,72] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    omega
  simpa [show 6*m/3=2*m by omega,←Nat.mul_assoc] using exact_even_triples (6*m) mem

#print axioms exact_multiples_of_six
end WildSieve.EvenTriples
