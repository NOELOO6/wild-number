import GraphSieve
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
  classical
  apply exact_pair (by omega)
  intro g
  let f := fixedSize n
  let t := levels n
  have data : n=f+3*t ∧ (f=0 ∨ f=4 ∨ f=5) ∧ 2*t+(f-1)=(2*n+2)/3 := by
    by_cases h0 : n%3=0
    · simp [f,t,levels,fixedSize,h0]; omega
    by_cases h1 : n%3=1 <;> simp [f,t,levels,fixedSize,h0,h1] <;> omega
  let F := coloringFactor (augment odd g)
  have room (b : Nat) (lo : 1≤b) (hi : b≤f) : b+b.choose 2*b < Fintype.card (Fin (n+1)) := by
    have five : b≤5 := by omega
    have ch := Nat.choose_le_choose 2 five
    have limit : (5 : Nat).choose 2=10 := by decide
    rw [limit] at ch
    have mul := Nat.mul_le_mul ch five
    simp only [Fintype.card_fin]
    omega
  obtain ⟨B,rb,bs,rain⟩ := rainbow_at_root F (Fin.last n) f room
  have ws : Bᶜ.card=3*t := by rw [card_compl,Fintype.card_fin,bs]; omega
  obtain ⟨h,cert⟩ := checked
  obtain ⟨L,wins⟩ := frozen_layout F B (Fin.last n) f t rb bs ws rain h (by simpa only [Fintype.card_fin] using cert)
  rw [← data.2.2]
  exact upper_from_layout g odd B f t rb bs ws rain (by omega) L wins

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
