import NineRows
namespace NineNamed
abbrev Failure := Fin 10 × Fin 7
def sumBy (l : List Failure) (f : Nat → Nat → Int) := (l.map (fun (x,y) => f x y)).sum

theorem each : ∀ x : Fin 10, ∀ y : Fin 7,
    baseScore x y + extraScore x y ≤ 1000000*wins x y := by native_decide
theorem combine (l : List Failure) :
    sumBy l baseScore + sumBy l extraScore ≤ 1000000*sumBy l wins := by
  induction l with
  | nil => decide
  | cons p l ih =>
    have h := each p.1 p.2
    simp only [sumBy,List.map_cons,List.sum_cons] at *
    omega

theorem at_least_666 (l : List Failure)
    (singleCounts : sumBy l baseScore = 1401400*1000000+191800*(9*a 0+6*a 1))
    (accounts : 36*minGain[0]! + 54*minGain[1]! + 15*minGain[2]! ≤ sumBy l extraScore) :
    666 ≤ sumBy l wins := by
  have num : 1401400*1000000+191800*(9*a 0+6*a 1) +
        (36*minGain[0]! + 54*minGain[1]! + 15*minGain[2]!) = 665814250 := by native_decide
  have h := combine l
  omega
#print axioms at_least_666
end NineNamed
