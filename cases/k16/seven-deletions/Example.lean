import Seven
namespace AsymmetricDeletion

abbrev Edge := Nat × Nat
def a : List Edge := [(0,15),(1,10),(2,3),(4,6),(5,8),(7,9),(11,12),(13,14)]
def b : List Edge := [(7,15),(0,13),(1,14),(2,5),(3,11),(4,9),(6,10),(8,12)]
def fixed : List Edge := (14,15)::(List.range 7).map fun i => (i,7+i)
def fromEdges (es : List Edge) : Array Nat :=
  es.foldl (fun a (x,y) => (a.set! x y).set! y x) (Array.replicate 16 0)
def colors := (fixed :: [a,b].flatMap (fun es => (List.range 7).map (fun t =>
  es.map fun (u,v) => (Seven.rot u t,Seven.rot v t)))).toArray.map fromEdges
def proper := (Array.range 16).all fun v =>
  let ns := colors.map fun m => m[v]!
  (ns.toList.eraseDups.length == 15) && !(ns.contains v) &&
    colors.all (fun m => m[m[v]!]! == v)

def groups : List (List Nat) := [[4,14,15],[5,8,11],[1,7,10],[3,6,13],[2,9,12]]
def wild := groups.flatMap fun
  | [x,y,z] => [(x,y),(y,z)]
  | _ => []

/-- Direct path test on the remaining fifteen vertices, labeled 1 through 15. -/
def reach (m : Array Nat) : Nat := Id.run do
  let mut seen := 2
  for _ in [:15] do
    for v in [1:16] do
      if seen.testBit v && m[v]! != 0 then seen := seen ||| (1 <<< m[v]!)
    for (u,v) in wild do
      if seen.testBit u || seen.testBit v then seen := seen ||| (1 <<< u) ||| (1 <<< v)
  return seen

def weight (i j : Nat) : Nat := Id.run do
  if i == j then return 0
  let mut v := 0
  for n in [:8] do
    v := colors[j]![colors[i]![v]!]!
    if v == 0 then return (2*(n+1))^3
  return 0
def indices := Array.range 15
def first := indices.map fun i => (indices.map (weight i)).toList.sum
def scores := indices.map fun i => (indices.map fun j => weight i j * first[j]!).toList.sum

/-- The scores are invariant under simultaneous point and color permutations
    fixing 0. Different scores distinguish all fifteen colors. -/
theorem example_checked : proper = true ∧ wild.length = 10 ∧
    colors.all (fun m => reach m == 65534) = true ∧ scores.toList.eraseDups.length = 15 := by
  native_decide
#print axioms example_checked
end AsymmetricDeletion

namespace AsymmetricDeletion
/-- Switch colors 1 and 4 on the alternating cycle 4–6–5–8–7–9–14–13–4. -/
def switchedSide : List Nat := [4,6,5,8,7,9,14,13]
def switched := indices.map fun i => (Array.range 16).map fun v =>
  if switchedSide.contains v && (i == 1 || i == 4) then colors[5-i]![v]! else colors[i]![v]!
def newWild : List Edge := [(6,8),(8,10),(3,5),(5,7),(1,4),(4,9),(2,12),(12,15),(11,13),(13,14)]

def cycleWeight (v i j : Nat) : Nat := Id.run do
  let mut u := v
  for d in [:8] do
    u := switched[j]![switched[i]![u]!]!
    if u == v then return (2*(d+1))^3
  return 0

def pointScores := (Array.range 16).map fun v =>
  (indices.map fun i => ((Array.range i).map (cycleWeight v i)).toList.sum).toList.sum

def postReach (m : Array Nat) : Nat := Id.run do
  let mut seen := 2
  for _ in [:15] do
    for v in [1:16] do
      if seen.testBit v && m[v]! != 0 then seen := seen ||| (1 <<< m[v]!)
    for (u,v) in newWild do
      if seen.testBit u || seen.testBit v then seen := seen ||| (1 <<< u) ||| (1 <<< v)
  return seen

theorem asymmetric_sixteen :
    (Array.range 16).all (fun v =>
       ((switched.map fun m => m[v]!).toList.eraseDups.length == 15) &&
       (switched.all fun m => m[v]! != v && m[m[v]!]! == v)) = true ∧
    pointScores.toList.eraseDups.length = 16 ∧ newWild.length = 10 ∧
    switched.all (fun m => postReach m == 65534) = true := by native_decide
#print axioms asymmetric_sixteen
end AsymmetricDeletion
