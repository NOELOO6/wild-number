import Protected
namespace ProtectedExample
set_option interpreter.prefer_native true

def colors := ((include_str "example.txt").trim.splitOn "\n").toArray.map
  fun row => ((row.splitOn " ").filterMap String.toNat?).toArray

def proper := colors.size == 15 && (Array.range 16).all fun v =>
  (colors.map (fun m => m[v]!)).toList.eraseDups.length == 15 &&
    colors.all (fun m => m.size == 16 && m[v]! != v && m[m[v]!]! == v)

def rootedType (m : Array Nat) : List Nat := Id.run do
  let mut left := 65535
  let mut result := #[]
  for _ in [:4] do
    if left == 0 then break
    let start := (left ^^^ (left &&& (left-1))).log2
    let mut v := start
    let mut n := 0
    for _ in [:8] do
      let w := colors[0]![v]!
      left := left ^^^ Protected.bit v ^^^ Protected.bit w
      v := m[w]!
      n := n+2
      if v == start then break
    result := result.push n
  return result[0]! :: result.toList.tail.mergeSort

theorem ten_test :
    (Protected.ca.all (· ≤ 83456)) = true ∧ Protected.ca[3]! = 31104 ∧
    10*31104 + 4*83456 < 645120 ∧ proper = true ∧
    (((colors.toList.drop 1).map rootedType).count [4,6,6] = 13) ∧
    (((colors.toList.drop 1).map rootedType).count [4,12] = 1) ∧
    645120-(13*31104+50304) = 190464 := by native_decide
#print axioms ten_test
end ProtectedExample
