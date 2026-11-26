import Std
namespace SearchExample
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def rows := ((include_str "search-coloring.json").splitOn "\n").filterMap fun line => Id.run do
  let nums := ((line.toList.map (fun c => if c.isDigit then c else ' ') |> String.mk).splitOn " ").filterMap String.toNat?
  if nums.length != 16 then return none
  return some nums.toArray
def bit (v : Nat) := 1 <<< v
def valid := rows.length == 15 && rows.all (fun m => (Array.range 16).all fun v =>
  m[v]! < 16 && m[v]! != v && m[m[v]!]! == v) &&
  (Array.range 16).all (fun v => (rows.map (fun m => m[v]!)).eraseDups.length == 15)
def closed : Array Bool := Id.run do
  let mut c := Array.replicate 65536 false
  for m in rows do
    let es := ((Array.range 16).filter fun a => a < m[a]!).map (fun a => bit a ||| bit m[a]!)
    for i in [0:8] do
      for j in [0:i] do
        let q := es[i]! ||| es[j]!
        c := c.set! q true
        for k in [0:j] do c := c.set! (q ||| es[k]!) true
  return c

def groups (root : Nat) := (Array.range 16).map fun a => Id.run do
  let mut out := #[]
  for b in [a+1:16] do
    for c in [b+1:16] do
      let t := bit a ||| bit b ||| bit c
      if !t.testBit root && !closed[bit root ||| t]! then out := out.push t
  return out

def least : Array Nat := Id.run do
  let mut v := #[0]
  for x in [1:65536] do v := v.push (if x%2 == 1 then 0 else 1+v[x/2]!)
  return v
def count (gs : Array (Array Nat)) : Nat → Nat → List Nat → Nat
  | 0, left, _ => if left == 0 then 1 else 0
  | k+1, left, old => gs[least[left]!]!.foldl (fun acc t =>
    if left &&& t == t && old.all (fun s => !closed[s ||| t]!) then
      acc + count gs k (left ^^^ t) (t::old) else acc) 0
def allCounts := (Array.range 16).map fun root => count (groups root) 5 (65535 ^^^ bit root) []
theorem concrete_counts : valid = true ∧ allCounts =
    #[109284,110660,109284,109284,106880,109284,109284,110660,
      109284,109284,112355,109284,109284,112355,109284,85250] ∧
    allCounts.toList.sum = 1731000 := by native_decide
#print axioms concrete_counts
end SearchExample
