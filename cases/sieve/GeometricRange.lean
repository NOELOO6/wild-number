import GeometricBounds

namespace WildSieve.Geometric
open Finset WildExact
set_option maxRecDepth 100000
set_option maxHeartbeats 0


private def passes (n : Nat) : Bool :=
  let f := fixedSize n
  let t := levels n
  let b := rate (t/2)
  decide ((degree n f t 1:ℚ)*sealWeight t 1*b^3+(degree n f t 2:ℚ)*sealWeight t 2*b^6≤b-1) &&
    decide ((∑ j∈longLevels t,(countBound n f t j:ℚ)*sealWeight t j*b^(3*j))<1)

private theorem exact_pass (n : Nat) (lo : 55≤n) (odd : n%2=1) (ok : passes n=true) :
    (∀ g : Coloring n n,Exact g ((2*n+2)/3)) ∧ (∀ g : Coloring (n+1) n,Exact g ((2*n+2)/3)) := by
  obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp ok
  have one : 1≤rate (levels n/2) := by unfold rate;exact le_add_of_nonneg_right (div_nonneg (by decide) (Nat.cast_nonneg _))
  have c := cert n (fixedSize n) (levels n) _ one (of_decide_eq_true a) (of_decide_eq_true b)
  apply exact_from_rule n lo odd
  intro F B r hr bs ws rain
  exact frozen_layout F B r _ _ hr bs ws rain _ (by simpa only [Fintype.card_fin] using c)

private def block (d k : Nat) := (List.range k).all (fun i => passes (d+2*i))

private theorem checked : block 155 526=true := by native_decide

/-- The same geometric comparison applies at every odd order 155 through
1205 and gives the exact value at each following even order as well. -/
theorem medium (n : Nat) (lo : 155≤n) (hi : n≤1205) (odd : n%2=1) :
    (∀ g : Coloring n n,Exact g ((2*n+2)/3)) ∧ (∀ g : Coloring (n+1) n,Exact g ((2*n+2)/3)) := by
  have h := List.all_eq_true.mp checked ((n-155)/2) (List.mem_range.mpr (by omega))
  rw [show 155+2*((n-155)/2)=n by omega] at h
  exact exact_pass n (by omega) odd h

#print axioms medium
end WildSieve.Geometric
