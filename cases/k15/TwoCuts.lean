import HalfSplits

namespace TwoCuts
open HalfSplits
set_option maxHeartbeats 0

/-- A split is represented by the half that does not contain point 11. -/
def points (s : Nat) := ((List.range 12).filter s.testBit).length
def sides := (List.range 2048).filter fun s => points s == 6
def distance (s t : Nat) := let k := points (s &&& t); min k (6-k)
def entries2 : Array Int := #[90,35,2,-9]
def entries6 : Array Int := #[60,-10,4,-3]
def value (e : Array Int) (s t : Nat) := e[distance s t]?.getD 0
def first := 63
def representatives : List Nat := [63,95,207,455]
def gram (e : Array Int) (s t : Nat) : Int :=
  (sides.map fun u => value e s u * value e u t).sum
def isAdjacent (s t : Nat) : Int := if distance s t = 3 then 1 else 0
def isEqual (s t : Nat) : Int := if s=t then 1 else 0

theorem all_distances : representatives.map (distance first) = [0,1,2,3] ∧
    sides.length = 462 := by native_decide

/-- Permutation symmetry reduces each entry of either square to four checks. -/
theorem two_gram_matrices : representatives.all (fun t =>
    gram entries2 first t == 770 * value entries2 first t &&
    gram entries6 first t == 210 * value entries6 first t) = true := by native_decide

/-- After multiplication by 2310 this is the decomposition into two
    positive semidefinite matrices. -/
theorem decomposition : representatives.all (fun t =>
    2310*(8*isEqual first t-isAdjacent first t)+960 ==
      84*value entries2 first t+198*value entries6 first t) = true := by native_decide

def pairLimit (b : Nat) := (192*b*b/462+8*b)/2
theorem small_mark_set : pairLimit 84 = 1802 ∧
    (List.range 85).all (fun b => pairLimit b ≤ 1802) = true := by native_decide
theorem pair_budget : pairLimit 96 = 2299 ∧
    (List.range 97).all (fun b => pairLimit b ≤ 2299) = true := by native_decide

/-- The two nonnegative quadratic forms are integers on a set indicator.
    At 96 marks, attaining 2299 would force 84*u + 198*v = 60. -/
theorem integer_pair_limit (b e u v : Nat) (hb : b ≤ 96)
    (he : e ≤ pairLimit b)
    (identity : (2310 : Int)*(8*(b : Int)-2*(e : Int))+960*(b : Int)^2 =
      84*(u : Int)+198*(v : Int)) : e ≤ 2298 := by
  have small : (List.range 96).all (fun z => pairLimit z ≤ 2298) = true := by native_decide
  by_cases h : b < 96
  · have bound := List.all_eq_true.mp small b (List.mem_range.mpr h)
    exact Nat.le_trans he (of_decide_eq_true bound)
  · have h96 : b = 96 := by omega
    subst b
    have top : pairLimit 96 = 2299 := by decide
    rw [top] at he
    by_cases hsmall : e ≤ 2298
    · exact hsmall
    · have eq : e = 2299 := by omega
      subst e
      change 60 = 84*(u : Int)+198*(v : Int) at identity
      omega

/-- Pack the remaining losses into bins of capacity c to maximize their squares. -/
def lossSquares (h : Nat) := ((List.range (min 27 h+1)).map fun z =>
  let c := min z (h+9-z)
  let v := 3*h-z
  if v ≤ 11*c then z*z + v/c*c*c + (v%c)^2 else 0).foldl max 0
def vertexLimit (m : Nat) := let h := 75-m
  min ((51*m+243)/2) ((4068+lossSquares h-105*h)/2)
def countBound (m : Nat) (p : Price) : Nat :=
  let sum := 462*p.fixed + 84*(m : Int)*p.first +
    p.square*(21*(vertexLimit m : Int)-14*(choose2 m : Int))
  ((sum+3*p.den-1)/(3*p.den)).toNat
def guaranteed (m : Nat) := max (15400-280*m) ((countPrices.map (countBound m)).foldl max 0)
theorem repeated_triples : (List.range 64).all (fun m =>
    decide (2316 ≤ guaranteed m)) = true := by native_decide
theorem thresholds : ([⟨64,94⟩,⟨65,93⟩,⟨66,91⟩,⟨67,91⟩,⟨68,91⟩,⟨69,91⟩,
    ⟨70,91⟩,⟨71,90⟩,⟨72,89⟩,⟨73,88⟩,⟨74,86⟩,⟨75,84⟩] : List (Nat × Nat)).all
    (fun (m,b) => decide (pairLimit b < guaranteed m)) = true := by native_decide
theorem survivors (all spoiled : Nat) (a : 1824 ≤ all) (b : spoiled ≤ 1802) :
    22 ≤ all-spoiled := by omega
#print axioms integer_pair_limit
#print axioms two_gram_matrices
#print axioms decomposition
#print axioms repeated_triples
end TwoCuts
