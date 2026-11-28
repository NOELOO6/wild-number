import GraphSieve
namespace WildSieve
local instance (priority := 2000) {m : Nat} : DecidableEq (Fin m) :=
  (inferInstance : LinearOrder (Fin m)).toDecidableEq
open Finset WildExact
/-- A rule for a particular coloring only needs partitions in its own
augmented matching system, at the distinguished extra vertex. -/
theorem upper_from_coloring_rule (n : Nat) (large : 55≤n) (odd : n%2=1) (g : Coloring n n)
    (rule : ∀ B : Finset (Fin (n+1)), Fin.last n∈B → B.card=fixedSize n+1 →
      Bᶜ.card=3*levels n → Rainbow (coloringFactor (augment odd g)) B →
      ∃ L : Layout (univ : Finset (Free B)),∀ j∈shortLevels∪longLevels (levels n),
        ∀ X∈badScopes (coloringFactor (augment odd g)) B (Fin.last n) (fixedSize n) (levels n) j,
          L∉sealEvent X) : Upper g ((2*n+2)/3) := by
  classical
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
  obtain ⟨L,wins⟩ := rule B rb bs ws rain
  rw [← data.2.2]
  exact upper_from_layout g odd B f t rb bs ws rain (by omega) L wins

/-- Any rule that supplies a cut-free triple partition gives exact wild numbers at both orders. -/
theorem exact_from_rule (n : Nat) (large : 55≤n) (odd : n%2=1)
    (rule : ∀ (F : Factor (Fin (n+1)) (Fin n)) (B : Finset (Fin (n+1))) (r : Fin (n+1)),
      r∈B → B.card=fixedSize n+1 → Bᶜ.card=3*levels n → Rainbow F B →
      ∃ L : Layout (univ : Finset (Free B)),∀ j∈shortLevels∪longLevels (levels n),
        ∀ X∈badScopes F B r (fixedSize n) (levels n) j,L∉sealEvent X) :
    (∀ g : Coloring n n, Exact g ((2*n+2)/3)) ∧
    (∀ g : Coloring (n+1) n, Exact g ((2*n+2)/3)) := by
  classical
  apply exact_pair (by omega)
  intro g
  exact upper_from_coloring_rule n large odd g (fun B => rule _ B (Fin.last n))

end WildSieve
