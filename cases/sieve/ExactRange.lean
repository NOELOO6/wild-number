import GraphRule
import KernelTables
namespace WildSieve
local instance (priority := 2000) {m : Nat} : DecidableEq (Fin m) :=
  (inferInstance : LinearOrder (Fin m)).toDecidableEq
open Finset WildExact
/-- An arithmetic certificate gives the exact wild number at both orders. -/
theorem exact_from_cert (n : Nat) (large : 55≤n) (odd : n%2=1)
    (checked : ∃ h,Cert n (fixedSize n) (levels n) h) :
    (∀ g : Coloring n n, Exact g ((2*n+2)/3)) ∧
    (∀ g : Coloring (n+1) n, Exact g ((2*n+2)/3)) := by
  obtain ⟨h,cert⟩ := checked
  exact exact_from_rule n large odd fun F B r rb bs ws rain =>
    frozen_layout F B r _ _ rb bs ws rain h (by simpa only [Fintype.card_fin] using cert)

theorem exact_from_sieve (n : Nat) (large : 55≤n) (odd : n%2=1) (yes : accepts n=true) :
    (∀ g : Coloring n n, Exact g ((2*n+2)/3)) ∧
    (∀ g : Coloring (n+1) n, Exact g ((2*n+2)/3)) :=
  exact_from_cert n large odd (cert_of_accepts n yes)

#print axioms exact_from_sieve

/-- Every minimum proper coloring at the stated odd orders, and at each
following even order, attains the conjectured wild number. -/
theorem exact_medium (n : Nat) (lo : 83≤n) (hi : n≤153) (odd : n%2=1) :
    (∀ g : Coloring n n, Exact g ((2*n+2)/3)) ∧
    (∀ g : Coloring (n+1) n, Exact g ((2*n+2)/3)) := by
  exact exact_from_cert n (by omega) odd (medium_certificate n lo hi odd)

#print axioms exact_medium
end WildSieve
