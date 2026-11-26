import Std
namespace Protected
set_option maxRecDepth 200000
@[inline] def bit (v : Nat) := 1 <<< v
def types : Array (List Nat) := #[[4,4,4,4],[4,4,8],[8,4,4],[4,6,6],[6,4,6],
  [4,12],[12,4],[6,10],[10,6],[8,8],[16]]
def a : Array (List Nat) := #[[0],[1,2,4],[3,6,7],[5,8,10],[9,12,13],[11,14,15]]
def b : Array (List Nat) := #[[0],[1,2,4],[3,6,8],[5,7,10],[9,12,13],[11,14,15]]

def shifted (ls : List Nat) : Array Nat := Id.run do
  let mut m := Array.replicate 16 0
  let mut start := 0
  for n in ls do
    for j in [:n/2] do
      let u := start+2*j+1
      let v := start+(2*j+2)%n
      m := (m.set! u v).set! v u
    start := start+n
  return m

def closed (m : Array Nat) : Array Nat := Id.run do
  let mut sides := #[0]
  for v in [:16] do
    if v < m[v]! then
      let e := bit v ||| bit m[v]!
      sides := sides ++ sides.map (· ||| e)
  return sides

def bySide : Array Nat := Id.run do
  let mut table := Array.replicate 65536 0
  for i in [:types.size] do
    for s in closed (shifted types[i]!) do table := table.modify s (· ||| bit i)
  return table

def orders : Nat → List Nat → List (List Nat)
  | 0, _ => [[]]
  | k+1, xs => xs.flatMap fun v => (orders k (xs.erase v)).map (v :: ·)
def perms := (orders 7 [1,2,3,4,5,6,7]).toArray.map List.toArray

def relabel (perm : Array Nat) (flip : Nat) : Array Nat := (Array.range 16).map fun v =>
  if v < 2 then v else
    let i := v/2-1
    2*perm[i]! + ((v%2) ^^^ ((flip >>> i) &&& 1))

def masks (g : Array (List Nat)) (p : Array Nat) :=
  g.map fun block => block.foldl (fun s v => s ||| bit p[v]!) 0

def failed (g : Array Nat) (table : Array Nat) : Nat := Id.run do
  let mut z := 0
  for j in [:6] do
    for k in [:j] do z := z ||| table[g[j]! ||| g[k]!]!
  return z

def histogram (g : Array (List Nat)) : Array Nat := Id.run do
  let mut out := Array.replicate 2048 0
  for p in perms do
    for f in [:128] do
      out := out.modify (failed (masks g (relabel p f)) bySide) (·+1)
  return out

def counts (h : Array Nat) := (Array.range 11).map fun i => Id.run do
  let mut n := 0
  for v in [:h.size] do
    if v.testBit i then n := n+h[v]!
  return n

def ca := counts (histogram a)
def cb := counts (histogram b)
def rooted := (Array.range 11).map fun i => 649*ca[i]! + 351*cb[i]!

/-- Choose the root freely. A cycle of length n supplies n possible roots. -/
def unrooted (ls : List Nat) : Nat := (ls.map fun n =>
  let key := n :: ((ls.erase n).mergeSort)
  n * ca[types.toList.idxOf key]!).sum

def closedAnchor := (closed ((Array.range 16).map (· ^^^ 1))).foldl
  (fun (t : Array Nat) s => t.set! s 1) (Array.replicate 65536 0)
def valid (g : Array (List Nat)) :=
  (g.toList.map List.length == [1,3,3,3,3,3]) &&
  ((g.toList.flatten.mergeSort) == List.range 16) &&
  (failed (masks g (Array.range 16)) closedAnchor == 0)

end Protected
