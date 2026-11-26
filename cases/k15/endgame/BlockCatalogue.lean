import Std

/- A proof-tree checker for blocking all three-triple partitions of nine.
   The input contains graph representatives, relabelings, and search choices.
   Each choice is checked against the vertex-cover problem it claims to close. -/
namespace BlockCatalogue
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def numbers (s : String) : Array Nat :=
  ((s.splitOn " ").filterMap String.toNat?).toArray
def lines (s : String) := ((s.splitOn "\n").map numbers).toArray

def repsData := lines (include_str "graphs8.txt")
def treeData := lines (include_str "cert.tree")
def catalogue := (lines (include_str "cert.blocks")).filter (fun row => !row.isEmpty)
def cap := 43
def capFour := 34
def capSeven := 35

def fields (n width code : Nat) :=
  (Array.range n).map (fun i => (code >>> (i*width)) % (1 <<< width))
def perm (p : Array Nat) := (Array.range p.size).all (fun x => p.contains x)
def idx (a b : Nat) := let j := max a b; j*(j-1)/2+min a b
def chooseTwo (n : Nat) := n*(n-1)/2
def edgeMap (n g : Nat) (p : Array Nat) : Nat := Id.run do
  let mut image := 0
  for j in [:n] do
    for i in [:j] do
      if g.testBit (idx i j) then image := image ||| (1 <<< idx p[i]! p[j]!)
  return image

def found (sorted : Array Nat) (v : Nat) := sorted.binSearchContains v (· < ·)
def layer (n : Nat) (parents next codes : Array Nat) := Id.run do
  let width := 1 <<< (n-1)
  if codes.size != parents.size*width then return false
  for i in [:parents.size] do
    for newEdges in [:width] do
      let p := fields n 3 codes[i*width+newEdges]!
      if !perm p then return false
      let g := parents[i]! ||| (newEdges <<< chooseTwo (n-1))
      if !found next (edgeMap n g p) then return false
  return true
def coverGraphs := (Array.range 8).all fun k =>
  layer (k+1) (if k==0 then #[0] else repsData[2*k-2]!)
    repsData[2*k]! repsData[2*k+1]!
theorem eight_vertex_coverage : coverGraphs = true := by native_decide

def pc (v : UInt64) : Nat := Id.run do
  let v : UInt64 := v - ((v >>> 1) &&& (0x5555555555555555 : UInt64))
  let v : UInt64 := (v &&& (0x3333333333333333 : UInt64)) + ((v >>> 2) &&& (0x3333333333333333 : UInt64))
  let v : UInt64 := (v + (v >>> 4)) &&& (0x0f0f0f0f0f0f0f0f : UInt64)
  return (((v * (0x0101010101010101 : UInt64)) >>> 56) : UInt64).toNat
def bit (i : Nat) := (1 : UInt64) <<< i.toUInt64
def lo (x : UInt64) := x &&& (0-x)
def slot (x : UInt64) := ((x*(0x03f79d71b4cb0a89 : UInt64)) >>> 58).toNat
def logs := Id.run do
  let mut arr := Array.replicate 64 0
  for j in [:64] do arr := arr.set! (slot (bit j)) j
  return arr
def first (x : UInt64) := logs[slot (lo x)]!
def points (t : Nat) := (Array.range 9).filter (fun i => t.testBit i)
def triple := (Array.range 256).filter (fun s => (points s).size == 3)
def pairs8 := (Array.range 256).filter (fun s => (points s).size == 2)
def inverse (xs : Array Nat) := Id.run do
  let mut table := Array.replicate 512 0
  for i in [:xs.size] do table := table.set! xs[i]! i
  return table
def pairNumber := inverse pairs8
def tripleNumber := inverse triple
def neighbors := Id.run do
  let mut out := #[]
  for t in triple do
    let mut list := #[]
    for i in [:triple.size] do
      let u := triple[i]!
      if (t &&& u) == 0 then list := list.push (i, pairNumber[255 ^^^ t ^^^ u]!)
    out := out.push list
  return out
def adjacency (link : UInt64) := neighbors.map fun row => Id.run do
  let mut mask : UInt64 := 0
  for (i,e) in row do
    if (link &&& bit e) == 0 then mask := mask ||| bit i
  return mask

structure Concentration where
  kind : Nat
  rootMask : UInt64
  freeMask : UInt64
deriving Inhabited
def limits := (Array.range 512).map fun s => Id.run do
  let size := (points s).size
  let th := if size == 1 then 1 else if size == 4 then 2 else if size == 7 then 3 else 4
  let mut a : UInt64 := 0
  let mut b : UInt64 := 0
  for i in [:28] do
    if (points (s &&& (256 ||| pairs8[i]!))).size ≥ th then a := a ||| bit i
  for i in [:56] do
    if (points (s &&& triple[i]!)).size ≥ th then b := b ||| bit i
  return Concentration.mk size a b

def fromMask (p : Array Nat) (t : Nat) := (points t).foldl (fun s i => s ||| (1 <<< p[i]!)) 0
def subsetWitness (link chosen : UInt64) (index code : Nat) := Id.run do
  if index >= catalogue.size then return false
  let p := fields 9 4 code
  if !perm p then return false
  for t in catalogue[index]! do
    if (points t).size != 3 || t >= 512 then return false
    let old := fromMask p t
    if old >= 256 then
      if (link &&& bit pairNumber[old-256]!) == 0 then return false
    else
      if (chosen &&& bit tripleNumber[old]!) == 0 then return false
  return true

def greedy (adj : Array UInt64) (left : UInt64) := Id.run do
  let mut rem := left
  let mut count := 0
  for _ in [:56] do
    if rem == 0 then break
    let i := first rem
    rem := rem ^^^ lo rem
    let options := rem &&& adj[i]!
    if options != 0 then
      rem := rem ^^^ lo options
      count := count+1
  return count

structure TreeInput where
  link : UInt64
  degree : Nat
  adj : Array UInt64
  tokens : Array Nat

def checkTree (data : TreeInput) : Nat → UInt64 → UInt64 → Nat → Nat → Option Nat
  | 0, _, _, _, _ => none
  | fuel+1, left, chosen, budget, pos => do
    let tag ← data.tokens[pos]?
    if tag >= 512 then
      let r ← limits[tag-512]?
      let allowed ← match r.kind with
        | 1 => some data.degree
        | 4 => some capFour
        | 7 => some capSeven
        | _ => none
      guard (pc (chosen &&& r.freeMask) + pc (data.link &&& r.rootMask) > allowed)
      return pos+1
    if tag == 1 then
      guard (greedy data.adj left > budget)
      return pos+1
    if tag == 2 then
      let index ← data.tokens[pos+1]?
      let code ← data.tokens[pos+2]?
      guard (subsetWitness data.link chosen index code)
      return pos+3
    guard (16 ≤ tag && tag < 72)
    let j := tag-16
    let v := bit j
    guard ((v &&& left) != 0)
    let ns := data.adj[j]! &&& left
    let degree := pc ns
    guard (degree > 0)
    let next ← if budget > 0 then
      checkTree data fuel (left ^^^ v) (chosen ||| v) (budget-1) (pos+1)
      else some (pos+1)
    if degree <= budget then
      checkTree data fuel (left &&& ~~~(v ||| ns)) (chosen ||| ns) (budget-degree) next
    else return next

def graphRow (i g : Nat) := Id.run do
  let row := treeData[i]!
  let link := g.toUInt64
  let deg := pc link
  if deg < 10 || deg > cap then return row.isEmpty
  let data := TreeInput.mk link deg (adjacency link) row
  return checkTree data 58 ((bit 56)-1) 0 (cap-deg) 0 == some row.size

def allGraphs := repsData[14]!.zipIdx.all fun (g,i) => graphRow i g

theorem catalogue_covers : allGraphs = true := by native_decide
#print axioms eight_vertex_coverage
#print axioms catalogue_covers
end BlockCatalogue
