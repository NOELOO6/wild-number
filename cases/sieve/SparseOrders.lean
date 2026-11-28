import GraphRule
import RootTriples

namespace WildSieve.Sparse
open Finset WildExact
set_option maxRecDepth 100000
set_option maxHeartbeats 0

inductive Bound where
  | vertex (k : Nat)
  | pair (d : Nat)
deriving DecidableEq, Repr

def Bound.cost (b : Bound) (u : Nat) := match b with
  | .vertex k => k
  | .pair d => d*(u-1)/2

def Bound.holds {A C : Type} [LinearOrder A] [Fintype A] [Fintype C]
    (b : Bound) (F : Factor A C) (r : A) : Prop := match b with
  | .vertex k => VertexCap F r k
  | .pair d => PairCap F r d

private def degree (n f t : Nat) (b : Bound) (u j : Nat) :=
  if j=1 then min (shortDegree n f t u j) (b.cost u) else shortDegree n f t u j

private def passes (n : Nat) (b : Bound) : Bool :=
  let f := fixedSize n
  let t := levels n
  let deg := degree n f t b
  let h := comparisonTable deg t
  (List.range (3*t+1)).all (fun u => decide (DegreeOK deg t h u)) &&
    decide ((∑ j∈shortLevels∪longLevels t,lateCount n f t j*numerator t j*tableAt h (3*t-3*j))<
      ways t*tableAt h (3*t))

private theorem certificate (n : Nat) (b : Bound) (ok : passes n b=true) :
    ∃ h,SplitCertWith n (fixedSize n) (levels n) (degree n (fixedSize n) (levels n) b) h := by
  let t := levels n
  let f := fixedSize n
  let a := comparisonTable (degree n f t b) t
  obtain ⟨early,late⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨pos,localBound⟩ := local_of_checks (degree n f t b) t a early
  refine ⟨fun u => (tableAt a u:ℚ),pos,localBound,?_⟩
  have hp : 0<(ways t:ℚ) := by exact_mod_cast ways_pos t
  change (∑ j∈shortLevels∪longLevels t,(lateCount n f t j:ℚ)*(sealWeight t j*(tableAt a (3*t-3*j):ℚ)))<_
  rw [weighted,div_lt_iff₀ hp,mul_comm (tableAt a (3*t):ℚ)]
  exact_mod_cast of_decide_eq_true late

/-- Each entry is an order and a sufficient bound on distinct forbidden
triples through one vertex or one pair of vertices. -/
def cases : List (Nat × Bound) :=
  [(61,.pair 1),(67,.pair 1),(69,.pair 1),(73,.pair 1),(75,.pair 1),(65,.vertex 46),(67,.vertex 45),(69,.vertex 38),(71,.vertex 69),
   (73,.vertex 70),(75,.vertex 66),(71,.pair 2),(73,.pair 2),(75,.pair 2)]

private theorem checked : cases.all (fun k => decide (55≤k.1 ∧ k.1%2=1) && passes k.1 k.2)=true := by
  native_decide

/-- The exact wild number for every coloring satisfying any listed
incidence bound. The condition is on the coloring and the root alone. -/
theorem exact_of_cap {n : Nat} {b : Bound} (listed : (n,b)∈cases) (odd : n%2=1)
    (g : Coloring n n) (sparse : b.holds (coloringFactor (augment odd g)) (Fin.last n)) :
    Exact g ((2*n+2)/3) := by
  classical
  obtain ⟨lo,yes⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp checked (n,b) listed)
  have large : 55≤n := (of_decide_eq_true lo).1
  apply exact_of_upper _ (fun _ => odd_lower (by omega) g)
  apply upper_from_coloring_rule n large odd g
  intro B hr bs ws rain
  obtain ⟨h,cert⟩ := certificate n b yes
  apply frozen_split_with _ B (Fin.last n) _ _ hr bs ws rain (degree n (fixedSize n) (levels n) b) _ h
    (by simpa only [Fintype.card_fin] using cert)
  intro U z zu j _
  have raw := ordinary_degree _ B (Fin.last n) _ _ hr bs ws rain U z zu j
  simp only [Fintype.card_fin] at raw
  unfold degree
  split
  · rename_i one
    apply le_min raw
    subst j
    cases b with
    | vertex k => exact root_vertex_bound _ B _ hr k sparse U z
    | pair d => exact root_pair_bound _ B _ hr d sparse U z zu
  · exact raw

/-- The same numerical answer on the following even complete graph when
the indicated deletion satisfies the incidence bound. -/
theorem exact_of_sparse_deletion {n : Nat} {b : Bound} (listed : (n,b)∈cases) (odd : n%2=1)
    (g : Coloring (n+1) n) (sparse : b.holds (coloringFactor (augment odd (restrict g))) (Fin.last n)) :
    Exact g ((2*n+2)/3) := by
  obtain ⟨⟨w,legal,sz,win⟩,_⟩ := exact_of_cap listed odd (restrict g) sparse
  have lo : 55≤n := (of_decide_eq_true (Bool.and_eq_true_iff.mp (List.all_eq_true.mp checked (n,b) listed)).1).1
  exact exact_of_upper (upper_from_deletion g ⟨w,legal,sz.le,win⟩) (fun _ => even_lower (by omega) g)

#print axioms exact_of_cap
#print axioms exact_of_sparse_deletion
end WildSieve.Sparse
