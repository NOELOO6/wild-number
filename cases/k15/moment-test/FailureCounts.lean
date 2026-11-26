import Std
namespace FailureCounts
@[inline] def bit (v : Nat) := 1 <<< v
@[inline] def dropLow (s : Nat) := s &&& (s-1)
@[inline] def low (s : Nat) := s ^^^ dropLow s
def cyclic (c v : Nat) := if v == 15 then c else if v == c then 15 else (2*c+15-v)%15
def cuts (mate : Nat → Nat → Nat) : Array Nat := Id.run do
  let mut out := Array.replicate 65536 0
  for c in [:15] do
    let mut sides := #[0]
    for v in [:16] do
      if v < mate c v then
        let e := bit v ||| bit (mate c v)
        sides := sides ++ sides.map (· ||| e)
    for s in sides do out := out.modify s (· ||| bit c)
  return out
def pop : Array Nat := Id.run do
  let mut a := #[0]
  for i in [1:32768] do a := a.push (a[i/2]! + i%2)
  return a

/-- Choose the triple containing the least remaining point, then repeat.
    Each grouping is visited once. The root already forms its own block. -/
def count (table : Array Nat) (depth left : Nat) (groups : List Nat)
    (bad : Nat) (hist : Array Nat) : Array Nat := Id.run do
  match depth with
  | 0 => return hist.modify pop[bad]! (·+1)
  | n+1 =>
    let u := low left
    let mut second := dropLow left
    let mut acc := hist
    for _ in [:14] do
      if second == 0 then break
      let v := low second
      second := dropLow second
      let mut third := second
      for _ in [:13] do
        if third == 0 then break
        let g := u ||| v ||| low third
        third := dropLow third
        let next := groups.foldl (fun h t => h ||| table[g ||| t]!) bad
        acc := count table n (left ^^^ g) (g::groups) next acc
    return acc

def distribution (table : Array Nat) (r : Nat) :=
  count table 5 (65535 ^^^ bit r) [bit r] 0 (Array.replicate 16 0)
def cyclicCuts := cuts cyclic
def fifteen := distribution cyclicCuts 15
def allRoots (table : Array Nat) := (Array.range 16).foldl (fun acc r =>
  Array.zipWith (·+·) acc (distribution table r)) (Array.replicate 16 0)
def sixteen := allRoots cyclicCuts

def fake15 : Array Nat := #[0,781015,41104,317590,259775,155,0,0,0,0,0,0,1761,0,0,0]
def fake16 : Array Nat := #[0,11797640,2059080,4146520,4419160,0,0,0,0,0,0,0,0,0,0,0]
def moment (h : Array Nat) (d : Nat) := ((Array.range 16).map fun k => h[k]! * k^d).toList.sum
end FailureCounts
