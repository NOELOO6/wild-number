import ExactRange
import SplitLayout
namespace WildSieve
open Finset WildExact

private def splitTable (n f t : Nat) (a : Array Nat) : Bool :=
  (List.range (3*t+1)).all (fun u => decide (DegreeOK (shortDegree n f t) t a u)) &&
  decide ((∑ j∈shortLevels∪longLevels t,lateCount n f t j * numerator t j * tableAt a (3*t-3*j)) <
    ways t * tableAt a (3*t))

private theorem split_cert_of_table (n f t : Nat) (a : Array Nat) (yes : splitTable n f t a=true) :
    SplitCert n f t (fun u => (tableAt a u : ℚ)) := by
  obtain ⟨loc,tail⟩ := Bool.and_eq_true_iff.mp yes
  obtain ⟨pos,budget⟩ := local_of_checks (shortDegree n f t) t a loc
  refine ⟨pos,budget,?_⟩
  have h := of_decide_eq_true tail
  have hp : 0<(ways t : ℚ) := by exact_mod_cast ways_pos t
  rw [weighted,div_lt_iff₀ hp,mul_comm (tableAt a (3*t) : ℚ)]
  exact_mod_cast h

open Lean Elab Term in
elab "splitTable%(" n:num ")" : term => do
  let k := n.getNat
  let t := levels k
  return toExpr (comparisonTable (shortDegree k (fixedSize k) t) t)

local instance (priority := 2000) {m : Nat} : DecidableEq (Fin m) :=
  (inferInstance : LinearOrder (Fin m)).toDecidableEq
set_option maxRecDepth 200000
set_option maxHeartbeats 0

/-- Every minimum proper coloring of K79 and K80 has wild number 53. -/
theorem exact_K79_K80 : (∀ g : Coloring 79 79,Exact g 53) ∧ (∀ g : Coloring 80 79,Exact g 53) := by
  have cert := split_cert_of_table 79 4 25 (splitTable%(79)) (by decide)
  exact exact_from_rule 79 (by decide) (by decide) fun F B r hr bs ws rain =>
    frozen_split F B r 4 25 hr bs ws rain _ (by simpa only [Fintype.card_fin] using cert)

#print axioms exact_K79_K80
end WildSieve
