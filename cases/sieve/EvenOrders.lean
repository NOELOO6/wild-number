import EvenTriples
import KernelTables
namespace WildSieve.EvenTriples
open Finset WildExact

private def tableOK (n t : Nat) (a : Array Nat) :=
  (List.range (3*t+1)).all (fun u => decide (DegreeOK (pureDegree n t) t a u)) &&
  decide ((∑ j∈longLevels t,pureTotal n t j*numerator t j*tableAt a (3*t-3*j)) <
    ways t*tableAt a (3*t))

private theorem pure_exists {A C : Type} [LinearOrder A] [Fintype A] [Fintype C]
    (F : Factor A C) (r : A) (n t : Nat) (pts : Fintype.card A=n) (cols : Fintype.card C=n-1)
    (size : n=3*t) (a : Array Nat) (ok : tableOK n t a=true) :
    ∃ L : Layout (univ : Finset A),∀ j∈shortLevels∪longLevels t,∀ X∈cuts F r t j,L∉sealEvent X := by
  obtain ⟨loc,tail⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨pos,budget⟩ := local_of_checks (pureDegree n t) t a loc
  apply partition_from_counts t (pts.trans size) shortLevels (longLevels t) _ (fun j _ => cut_size F r t j)
    (fun j hj => by simp [shortLevels] at hj; omega) (pureDegree n t) (pureTotal n t)
    (fun U z hz j _ => pure_local F r t j U z hz n pts cols) (fun j _ => pure_global F r t j n pts cols)
    _ pos budget
  rw [weighted,div_lt_iff₀ (show (0:ℚ)<ways t by exact_mod_cast ways_pos t),mul_comm (tableAt a (3*t) : ℚ)]
  exact_mod_cast of_decide_eq_true tail

local instance (priority := 2000) orderFinEq {m : Nat} : DecidableEq (Fin m) :=
  (inferInstance : LinearOrder (Fin m)).toDecidableEq

private theorem exact_of_table (n t : Nat) (lo : 3≤n+1) (size : n+1=3*t)
    (a : Array Nat) (ok : tableOK (n+1) t a=true) (g : Coloring (n+1) n) : Exact g (2*t) := by
  obtain ⟨L,pass⟩ := pure_exists (coloringFactor g) (Fin.last n) (n+1) t (Fintype.card_fin _) (by simp) size a ok
  apply exact_of_upper (pure_upper g _ t size L pass)
  intro w le works
  have b := even_lower lo g le works
  omega

open Lean Elab Term in
elab "pureTables%(" lo:num "," count:num ")" : term => do
  return toExpr (List.range count.getNat |>.map fun i =>
    let n := lo.getNat+6*i
    (n,comparisonTable (pureDegree n (n/3)) (n/3)))

set_option maxRecDepth 200000
set_option maxHeartbeats 0
private def tables := pureTables%(48,5)
private theorem checked : tables.all (fun a => tableOK a.1 (a.1/3) a.2)=true := by decide
private theorem orders : tables.map Prod.fst=[48,54,60,66,72] := by decide

/-- Five even orders admit a winning partition entirely into triples. -/
theorem exact_even_triples (n : Nat) (hn : n∈[48,54,60,66,72]) :
    ∀ g : Coloring n (n-1), Exact g (2*(n/3)) := by
  have mem : n∈tables.map Prod.fst := orders ▸ hn
  obtain ⟨⟨k,a⟩,ha,rfl⟩ := List.mem_map.mp mem
  have yes := List.all_eq_true.mp checked _ ha
  have num : 3≤k ∧ k=3*(k/3) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
    omega
  cases k with
  | zero => omega
  | succ k => exact exact_of_table k _ num.1 num.2 a yes

#print axioms exact_even_triples
end WildSieve.EvenTriples
