import FilteredMoments
import GraphRule

namespace WildSieve.FilteredCuts
open Finset WildExact
local instance (priority := 2000) {n : Nat} : DecidableEq (Fin n) :=
  (inferInstance : LinearOrder (Fin n)).toDecidableEq
set_option maxHeartbeats 1000000
variable {A C V : Type} [Fintype A] [LinearOrder A] [Fintype C]
variable [Fintype V] [DecidableEq V]

/-- The remaining free sides after forbidding individual free triples. -/
noncomputable def otherScopes (F : Factor A C) (B : Finset A) (r : A) (f t : Nat) :=
  ((shortLevels ∪ longLevels t).erase 1).biUnion (badScopes F B r f t)

/-- Either cubic count suffices on the specified free vertex set. -/
def PositiveMoments (H K : Finset (Finset V)) (U : Finset V) : Prop :=
  6*first H K U+third H K U < 6*count H U []+3*second H K U ∨
  12*first H K U+third H K U < 12*count H U []+5*second H K U

theorem exists_survivor {H K : Finset (Finset V)} {U : Finset V} (test : PositiveMoments H K U) :
    ∃ L, L∈survivors H K U := by
  apply Finset.card_pos.mp
  rcases test with h|h
  · have b := cubic H K U; omega
  · have b := cubic_twelve H K U; omega

private theorem respects {X : Finset V} {L : Layout (univ : Finset V)} (ev : L∈sealEvent X) :
    ∀ b∈L.val,b⊆X ∨ Disjoint b X := by
  have wh := (seal_whole (subset_univ X) L).mp (local_seal_mem.mpr (mem_seal.mp ev))
  intro b hb
  by_cases d : Disjoint b X
  · exact Or.inr d
  obtain ⟨v,hv,vx⟩ := not_disjoint_iff.mp d
  exact Or.inl (wh b hb v hv vx)

/-- A surviving layout excludes every original closed-side event, including those next to a fixed block. -/
theorem scope_rule (F : Factor A C) (B : Finset A) (r : A) (f t : Nat)
    (test : PositiveMoments (badScopes F B r f t 1) (otherScopes F B r f t) univ) :
    ∃ L : Layout (univ : Finset (Free B)), ∀ j∈shortLevels∪longLevels t,
        ∀ X∈badScopes F B r f t j, L∉sealEvent X := by
  classical
  obtain ⟨L,hL⟩ := exists_survivor test
  obtain ⟨clean,rest⟩ := mem_sdiff.mp hL
  refine ⟨L,?_⟩
  intro j hj X hx ev
  by_cases one : j=1
  · subst j
    obtain ⟨D,_,xd⟩ := (mem_gather _ _ _).mp hx
    have size := (pull_mem.mp xd).1
    obtain ⟨M,inc⟩ := mem_seal.mp ev
    have num := M.property.1.card_vertices
    rw [M.property.2] at num
    obtain ⟨b,eq⟩ := card_eq_one.mp (show M.val.card=1 by omega)
    have bx : b=X := by simpa [vertices,eq] using M.property.2
    exact (mem_layouts.mp clean b (inc (by simp [eq]))).1 (bx ▸ hx)
  · apply rest (mem_biUnion.mpr ⟨X,mem_biUnion.mpr ⟨j,mem_erase.mpr ⟨one,hj⟩,hx⟩,?_⟩)
    exact mem_layouts.mpr fun b hb => ⟨(mem_layouts.mp clean b hb).1,fun S hS => mem_singleton.mp hS ▸ respects ev b hb⟩

/-- All three odd residue classes, including small orders, with a supplied rainbow fixed block. -/
theorem exact_fixed {n : Nat} (g : Coloring n n) (lo : 3≤n) (odd : n%2=1)
    (B : Finset (Fin (n+1))) (f t : Nat) (root : Fin.last n∈B)
    (size : B.card=f+1) (free : Bᶜ.card=3*t) (shape : f=0 ∨ f=4 ∨ f=5)
    (rain : Rainbow (coloringFactor (augment odd g)) B)
    (test : let F := coloringFactor (augment odd g)
        PositiveMoments (badScopes F B (Fin.last n) f t 1) (otherScopes F B (Fin.last n) f t) univ) :
    Exact g ((2*n+2)/3) := by
  classical
  obtain ⟨L,hL⟩ := scope_rule (coloringFactor (augment odd g)) B (Fin.last n) f t test
  have upper := upper_from_layout g odd B f t root size free rain (by omega) L hL
  have le := B.card_le_univ
  rw [Fintype.card_fin] at le
  rw [card_compl,Fintype.card_fin] at free
  have eq : 2*t+(f-1)=(2*n+2)/3 := by rcases shape with h|h|h <;> omega
  rw [eq] at upper
  exact exact_of_upper upper (fun _ => odd_lower lo g)

/-- A uniform set of moment estimates gives the conjectured number for both adjacent orders. -/
theorem exact_pair_of_moments {n : Nat} (large : 55≤n) (odd : n%2=1)
    (test : ∀ (F : Factor (Fin (n+1)) (Fin n)) (B : Finset (Fin (n+1))) (r : Fin (n+1)),
      r∈B → B.card=fixedSize n+1 → Bᶜ.card=3*levels n → Rainbow F B →
      PositiveMoments (badScopes F B r (fixedSize n) (levels n) 1)
        (otherScopes F B r (fixedSize n) (levels n)) univ) :
    (∀ g : Coloring n n, Exact g ((2*n+2)/3)) ∧
    (∀ g : Coloring (n+1) n, Exact g ((2*n+2)/3)) :=
  exact_from_rule n large odd (fun F B r rb bs ws rain => scope_rule F B r _ _ (test F B r rb bs ws rain))

#print axioms exact_fixed
#print axioms exact_pair_of_moments
end WildSieve.FilteredCuts
