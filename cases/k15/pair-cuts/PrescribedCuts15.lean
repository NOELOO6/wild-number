import TwoCuts

namespace PrescribedCuts15
open TwoCuts

/-- The entries of 21 times the split adjacency matrix plus 420 I minus 10 J. -/
def lowerGram : Array Int := #[410,-10,-10,11]

theorem gram_square : representatives.all (fun t =>
    gram lowerGram first t + 378 * value entries6 first t == 588 * value lowerGram first t &&
    value lowerGram first t == 21*isAdjacent first t+420*isEqual first t-10) = true := by
  native_decide

def score (x y : Nat) : Int :=
  3-3*(x : Int)-3*y+2*(HalfSplits.choose2 y : Int)+x*y

theorem pointwise (x y : Nat) (hx : x ≤ 4) (hy : y ≤ 3) :
    score x y ≤ (if x=0 ∧ y=0 then 3 else 0) := by
  have cert : (List.range 5).all (fun i => (List.range 4).all (fun j =>
    decide (score i j ≤ (if i=0 ∧ j=0 then 3 else 0)))) = true := by decide
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp cert x
    (List.mem_range.mpr (by omega))) y (List.mem_range.mpr (by omega)))

def splitLabels (f : Nat) := 96+4*f
def blockLabels (f : Nat) := 24-4*f
def splitPairs (b : Nat) := (10*b*b+41-420*b)/42
def incidences (f e b : Nat) :=
  11*e+2*(e-(blockLabels f-(9+f)))-(splitLabels f-b)*min e (15-f)
def target (f : Nat) := ([844,1521,2204,2892][f]?).getD 0

def totalScore (f e b : Nat) : Int :=
  3*(15400-280*(e : Int)-100*b)+2*(splitPairs b : Int)+10*(incidences f e b : Int)

private theorem table : (List.range 4).all (fun f =>
    (List.range (blockLabels f+1)).all (fun e =>
    (List.range (splitLabels f+1)).all (fun b =>
    decide (3*((target f : Int)-1) < totalScore f e b)))) = true := by native_decide

/-- The summed pointwise inequality, the eigenvalue bound and the two
incidence estimates suffice at every admissible pair of distinct counts. -/
theorem survivor_bound (f e b survivors : Nat) (hf : f ≤ 3) (he : e ≤ blockLabels f)
    (hb : b ≤ splitLabels f) (counted : totalScore f e b ≤ 3*(survivors : Int)) :
    target f ≤ survivors := by
  have cert := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp table f
    (List.mem_range.mpr (by omega))) e (List.mem_range.mpr (by omega))) b (List.mem_range.mpr (by omega))
  have strict := of_decide_eq_true cert
  omega

theorem target_values : [0,1,2,3].map target = [844,1521,2204,2892] := by decide

#print axioms gram_square
#print axioms survivor_bound
end PrescribedCuts15
