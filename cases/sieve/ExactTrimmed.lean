import ExactRange
import TrimmedLayout
namespace WildSieve
open Finset WildExact

private def trimmedTable (n f t : Nat) (a : Array Nat) : Bool :=
  (List.range (3*t+1)).all (fun u => decide (LocalOK n f t a u)) &&
  decide ((∑ j∈longLevels t,trimmedCount n f t j * ways (t-j) * tableAt a (3*t-3*j)) <
    ways t * tableAt a (3*t))

private theorem trim_cert_of_table (n f t : Nat) (a : Array Nat) (yes : trimmedTable n f t a=true) :
    TrimCert n f t (fun u => (tableAt a u : ℚ)) := by
  obtain ⟨loc,tail⟩ := Bool.and_eq_true_iff.mp yes
  obtain ⟨pos,budget⟩ := local_of_checks (degBound n f t) t a loc
  refine ⟨pos,budget,?_⟩
  have h := of_decide_eq_true tail
  have hp : 0<(ways t : ℚ) := by exact_mod_cast ways_pos t
  have scale : ∀ j,(trimmedCount n f t j : ℚ) * ((ways (t-j):ℚ)/ways t*(tableAt a (3*t-3*j):ℚ)) =
    (↑(trimmedCount n f t j * ways (t-j) * tableAt a (3*t-3*j)):ℚ)/(ways t:ℚ) := by
    intro j
    push_cast
    simp only [div_eq_mul_inv]
    ac_rfl
  simp only [scale]
  simp only [div_eq_mul_inv,←Finset.sum_mul,←Nat.cast_sum]
  rw [←div_eq_mul_inv,div_lt_iff₀ hp,mul_comm (tableAt a (3*t) : ℚ)]
  exact_mod_cast h

local instance (priority := 2000) trimmedFinEq {m : Nat} : DecidableEq (Fin m) :=
  (inferInstance : LinearOrder (Fin m)).toDecidableEq
set_option maxRecDepth 200000
set_option maxHeartbeats 0
private def comparison := (sieveTables%(77,1)).head!.2

/-- Every minimum proper coloring of K77 and K78 has wild number 52. -/
theorem exact_K77_K78 : (∀ g : Coloring 77 77,Exact g 52) ∧ (∀ g : Coloring 78 77,Exact g 52) := by
  have cert := trim_cert_of_table 77 5 24 comparison (by decide)
  exact exact_from_rule 77 (by decide) (by decide) fun F B r hr bs ws rain =>
    frozen_trimmed F B r 5 24 hr bs ws rain (Or.inr (by decide)) _
      (by simpa only [Fintype.card_fin] using cert)

#print axioms exact_K77_K78
end WildSieve
