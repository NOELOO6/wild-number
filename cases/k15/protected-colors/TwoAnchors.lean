import Protected
namespace TwoAnchors
open Protected (bit)
set_option maxRecDepth 200000

def cardinalRanks : Array Nat := Id.run do
  let mut size := #[0]
  let mut ranks := Array.replicate 17 0
  let mut out := #[]
  for x in [:65536] do
    if x > 0 then size := size.push (size[x/2]! + x%2)
    let n := size[x]!
    out := out.push ranks[n]!
    ranks := ranks.modify n (·+1)
  return out

/-- The smaller of the two six-sets never contains the highest available
    vertex. It always omits vertex 15 or the four-set already contains 15. -/
@[inline] def key (free : Bool) (r s : Nat) :=
  let rootSide := if free then r else r >>> 1
  cardinalRanks[rootSide]!*5005 + cardinalRanks[min s (65535 ^^^ r ^^^ s)]!

structure Fine where
  r : Nat
  x : Nat
  y : Nat
  deriving Inhabited

def templateFine : Array Fine := Id.run do
  let mut out := #[]
  for i in [1:6] do
    let rest := ((List.range' 1 5).erase i).toArray
    for j in [1:4] do out := out.push ⟨i,rest[0]!,rest[j]!⟩
  return out

structure Tables where
  total : Nat
  coarse : Array Nat
  fine : Array Nat

def orders8 := (Protected.orders 8 [0,1,2,3,4,5,6,7]).toArray.map List.toArray
def relabel8 (p : Array Nat) (flip : Nat) := (Array.range 16).map fun v =>
  2*p[v/2]! + ((v%2) ^^^ ((flip >>> (v/2)) &&& 1))

def collect (free : Bool) (i : Nat) : Tables := Id.run do
  let mut coarse := Array.replicate 65536 0
  let mut fine := Array.replicate ((if free then 1820 else 455)*5005) 0
  let mut total := 0
  let seeds := if free then #[(Protected.a,1)] else #[(Protected.a,649),(Protected.b,351)]
  let perms := if free then orders8 else Protected.perms
  for p in perms do
    for f in [:(if free then 256 else 128)] do
      let perm := if free then relabel8 p f else Protected.relabel p f
      for (layout,w) in seeds do
        let g := Protected.masks layout perm
        if !(Protected.failed g Protected.bySide).testBit i then
          total := total+w
          for j in [1:6] do
            for k in [:j] do coarse := coarse.modify (g[j]! ||| g[k]!) (·+w)
          for t in templateFine do
            let r := g[0]! ||| g[t.r]!
            let s := g[t.x]! ||| g[t.y]!
            fine := fine.modify (key free r s) (·+w)
  return ⟨total,coarse,fine⟩

structure Split where
  i : Nat
  j : Nat
  ways : Array (Nat × Nat × Nat)
  deriving Inhabited

def splits (free : Bool) : Array Split := Id.run do
  let mut out := #[]
  for i in [1:8] do
    for j in [:i] do
      if free || j == 0 then
        let rest := (((List.range 8).erase i).erase j).toArray
        let mut ways := #[]
        for h in [1:6] do
          for k in [1:h] do ways := ways.push (rest[0]!,rest[h]!,rest[k]!)
        out := out.push ⟨i,j,ways⟩
  return out

def freeSplits := splits true
def fixedSplits := splits false

def losses (table : Tables) (free : Bool) (es : Array Nat) : Nat := Id.run do
  let mut raw := 0
  for i in [1:8] do
    for j in [:i] do
      let s := es[i]! ||| es[j]!
      if free || j == 0 then raw := raw + table.coarse[s]!
      for k in [:j] do
        if free || k > 0 then raw := raw + table.coarse[s ||| es[k]!]!
  let mut correction := 0
  for split in (if free then freeSplits else fixedSplits) do
    let r := es[split.i]! ||| es[split.j]!
    for (x,y,z) in split.ways do
      let s := es[x]! ||| es[y]! ||| es[z]!
      correction := correction + table.fine[key free r s]!
  return raw-2*correction

@[inline] def dropLow (s : Nat) := s &&& (s-1)
@[inline] def low (s : Nat) := s ^^^ dropLow s

def checkMatchings (b : Array Nat) (check : Array Nat → Bool) (depth left : Nat)
    (es : Array Nat) : Bool := Id.run do
  match depth with
  | 0 => return check es
  | n+1 =>
    let x := low left
    let u := x.log2
    let rest := dropLow left
    let mut opts := rest &&& (65535 ^^^ (bit (u ^^^ 1) ||| bit b[u]!))
    for _ in [:15] do
      if opts == 0 then break
      let y := low opts
      opts := dropLow opts
      if !checkMatchings b check n (rest ^^^ y) (es.push (x ||| y)) then return false
    return true

def fixedCheck (i : Nat) : Bool := Id.run do
  let b := Protected.shifted Protected.types[i]!
  let t := collect false i
  if t.total != 645120000-Protected.rooted[i]! then return false
  return checkMatchings b (fun es => 15*losses t false es < 2*t.total) 8 65535 #[]

end TwoAnchors

namespace TwoAnchors
structure PriceRow where
  cycles : List Nat
  total : Nat
  premium : Nat
  prices : Array Nat
  deriving Inhabited

def freePrices : Array PriceRow :=
  ((include_str "free-prices.txt").trim.splitOn "\n").toArray.map (fun row =>
    let ns := (row.splitOn " ").filterMap String.toNat?
    let n := ns.head!
    ⟨ns.tail.take n, ns[n+1]!, ns[n+2]!, (ns.drop (n+3)).toArray⟩)

def anchor := (Array.range 16).map (· ^^^ 1)

def twoEights (a b : Array Nat) : Bool := (Array.range 16).all fun x =>
  let step := fun u : Nat => b[a[u]!]!
  let half := step (step x)
  half != x && step (step half) == x

def fromEdges (es : Array Nat) : Array Nat := Id.run do
  let mut m := Array.replicate 16 0
  for e in es do
    let u := (low e).log2
    let v := (dropLow e).log2
    m := (m.set! u v).set! v u
  return m

def priceEdges (r : PriceRow) (es : Array Nat) : Nat := Id.run do
  let mut n := 0
  for e in es do
    let u := (low e).log2
    let v := (dropLow e).log2
    n := n+r.prices[v*(v-1)/2+u]!
  return n

def freeCheck (i : Nat) : Bool := Id.run do
  let r := freePrices[i]!
  let idx := Protected.types.toList.idxOf r.cycles
  if idx ≥ 11 || r.prices.size != 120 then return false
  let b := Protected.shifted r.cycles
  let t := collect true idx
  if t.total != r.total || r.prices.toList.sum+3*r.premium ≥ 2*t.total then return false
  return checkMatchings b (fun es => Id.run do
    let q := losses t true es
    let price := priceEdges r es
    if q > price then return false
    if 2*q ≤ price+r.premium then return true
    if r.cycles != [8,8] then return false
    let m := fromEdges es
    return !(twoEights anchor m && twoEights b m)) 8 65535 #[]
end TwoAnchors
