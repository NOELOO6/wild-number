import Std
namespace K19Count
/-- Every entry counts the remaining endpoints in one connected component.
Pair the first remaining endpoint with an endpoint of component j. -/
def counts : Nat → List Nat → Nat × Nat
  | _, [] => (1,0)
  | 0, _::_ => (0,0)
  | fuel+1, a::tail => ((a::tail).zipIdx).foldl (fun (total,components) (b,j) =>
      let ways := if j == 0 then a-1 else b
      if ways == 0 then (total,components) else
      let remaining := if j == 0 then a-2 else a+b-2
      let others := if j == 0 then tail else tail.eraseIdx (j-1)
      let next := if remaining == 0 then others else remaining :: others
      let (t,c) := counts fuel next
      (total+ways*t, components+ways*(c+(if remaining == 0 then t else 0)))) (0,0)

def first := counts 10 [1,4,3,3,3,3,3]
theorem total_and_components : first = (654729075,723411000) := by native_decide
theorem exact_deficit : (first.2-first.1)*19*1309 = 2609*first.1 ∧
    (first.2-first.1)*19 < 2*first.1 := by rw [total_and_components]; decide
#print axioms exact_deficit
end K19Count
