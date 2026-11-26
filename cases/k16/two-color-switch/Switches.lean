import Seven
namespace SevenSwitch
set_option maxRecDepth 200000

abbrev M := Array Nat
@[inline] def bit (i : Nat) := 1 <<< i
@[inline] def dropLow (m : Nat) := m &&& (m-1)
@[inline] def lowBit (m : Nat) := m ^^^ dropLow m
def vertices := Array.range 16
def layouts (s : String) := ((s.trim.splitOn "\n").toArray.map fun l =>
  (l.splitOn " ").filterMap String.toNat?)
def fixedLayouts := layouts (include_str "fixed.txt")
def movingLayouts := layouts (include_str "moving.txt")
def goodLayout (root : Nat) (g : List Nat) := g.length == 5 &&
  g.all (fun s => s < 65536 && (vertices.filter s.testBit).size == 3) &&
  g.foldl (· ||| ·) 0 == 65535 ^^^ bit root

def cuts : Array Nat := Id.run do
  let mut table := Array.replicate 65536 0
  for (r,offset,groups) in [(15,0,fixedLayouts),(0,512,movingLayouts)] do
    for i in [:groups.size] do
      let g := groups[i]!.toArray
      for j in [:5] do
        table := table.modify (g[j]! ||| bit r) (· ||| bit (offset+i))
        for k in [:j] do table := table.modify (g[j]! ||| g[k]!) (· ||| bit (offset+i))
  return table

def allBits := bit 1024 - 1
def indexTable (depth left : Nat) (edges pairs : List Nat) (bad : Nat)
    (out : Array Nat) : Array Nat := Id.run do
  match depth with
  | 0 => return out.push (allBits ^^^ bad)
  | n+1 =>
    let u := lowBit left
    let rest := dropLow left
    let mut opts := rest
    let mut acc := out
    for _ in [:15] do
      if opts == 0 then break
      let v := lowBit opts
      opts := dropLow opts
      let e := u ||| v
      let b := edges.foldl (fun z t => z ||| cuts[e ||| t]!) bad
      let b := pairs.foldl (fun z t => z ||| cuts[e ||| t]!) b
      let p := if n == 0 then [] else edges.foldl (fun p t => (e ||| t)::p) pairs
      acc := indexTable n (rest ^^^ v) (e::edges) p b acc
    return acc

def wins := indexTable 8 65535 [] [] 0 (Array.mkEmpty 2027025)
def pop : Array Nat := Id.run do
  let mut a := #[0]
  for i in [1:65536] do a := a.push (a[i/2]! + i%2)
  return a

/-- Lexicographic rank of the matching which takes a on side and b elsewhere.
    All callers pass unions of entire alternating cycles. -/
def rank (a b : M) (side : Nat) : Nat := Id.run do
  let mut remaining := 65535
  let mut id := 0
  for j in [:7] do
    let u := (lowBit remaining).log2
    remaining := dropLow remaining
    let v := bit (if side.testBit u then a[u]! else b[u]!)
    id := (15-2*j)*id + pop[remaining &&& (v-1)]!
    remaining := remaining ^^^ v
  return id

def fromBase (p : Nat) (s : Seven.Base) : M := Id.run do
  let mut m := ((Array.replicate 16 0).set! p 15).set! 15 p
  for v in [:15] do
    for u in [:v] do
      if s.edges.testBit (Seven.idx u v) then m := (m.set! u v).set! v u
  return m

def rotate (m : M) (d : Nat) : M := Id.run do
  let mut out := Array.replicate 16 0
  for v in vertices do out := out.set! (Seven.rot v d) (Seven.rot m[v]! d)
  return out

def fixedColor : M := vertices.map fun v =>
  if v == 15 then 14 else if v == 14 then 15 else if v < 7 then v+7 else v-7

def cycleMask (a b : M) (start : Nat) : Nat := Id.run do
  let mut s := 0
  let mut v := start
  for _ in [:8] do
    let w := a[v]!
    s := s ||| bit v ||| bit w
    v := b[w]!
    if v == start then break
  return s

/-- Keep only layouts that work for every possible recoloring of a and b.
    The two original matchings already work on every input layout. -/
def robust (a b : M) (normal : Nat) : Nat := Id.run do
  let first := cycleMask a b 0
  if first == 65535 then return normal
  let mut rest := 65535 ^^^ first
  let mut sides := #[0,first]
  for _ in [:3] do
    if rest == 0 then break
    let c := cycleMask a b (lowBit rest).log2
    sides := sides ++ sides.map (· ||| c)
    rest := rest ^^^ c
  let mut result := normal
  for k in [1:sides.size-1] do
    result := result &&& wins[rank a b sides[k]!]!
  return result

structure Entry where
  tag : Nat
  orbit : Array M
  normal : Nat
  within : Array Nat
  deriving Inhabited

def entry (p : Nat) (s : Seven.Base) : Entry := Id.run do
  let m := fromBase p s
  let orbit := (Array.range 7).map (rotate m)
  let normal := orbit.foldl (fun z n => z &&& wins[rank n n 0]!) allBits
  let mut within := #[]
  for i in [:7] do
    within := within.push (robust orbit[i]! fixedColor normal)
    for d in [1:4] do within := within.push (robust orbit[i]! orbit[(i+d)%7]! normal)
  return ⟨s.tag,orbit,normal,within⟩

def as := ((Seven.bases 0).map (entry 0)).toArray
def bs := (Seven.bases 7).foldl (fun (a : Array (List Entry)) s =>
  a.modify s.tag (entry 7 s :: ·)) (Array.replicate 65536 [])
@[inline] def bothRoots (z : Nat) := (z &&& (bit 512 - 1)) != 0 && (z >>> 512) != 0

def withinOK (a b : Entry) :=
  (a.within.all fun mask => bothRoots (mask &&& b.normal)) &&
  (b.within.all fun mask => bothRoots (mask &&& a.normal))

def checkCross (a b : Entry) (s : Nat) : Bool := Id.run do
  let known := a.normal &&& b.normal
  for i in [:7] do
    if !bothRoots (robust a.orbit[i]! b.orbit[(i+s)%7]! known) then return false
  return true

def covered (which : Nat) : Bool := as.all fun a =>
  bs[65535 ^^^ a.tag]!.all (fun b => if which == 7 then withinOK a b else checkCross a b which)

def pairCount := (as.map fun a => bs[65535 ^^^ a.tag]!.length).toList.sum
end SevenSwitch
