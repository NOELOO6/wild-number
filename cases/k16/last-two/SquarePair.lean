import LastTwo
namespace SquarePair
open Prescribed

def square := canonical #[4,4,4,4]
def ca := closed square.1
def cb := closed square.2
def base := counts false square.1 square.2

def cuts (gs : Array Nat) : Array Nat := Id.run do
  let mut result := #[]
  for i in [1:6] do
    for j in [:i] do result := result.push (gs[j]! ||| gs[i]!)
  return result

def gather (depth left : Nat) (gs : Array Nat) (badA badB : Bool)
    (acc : Array (Array Nat)) : Array (Array Nat) := Id.run do
  match depth with
  | 0 => return if badA && badB then acc.push (cuts gs) else acc
  | d+1 =>
    let x := low left
    let mut ys := dropLow left
    let mut res := acc
    for _ in [:14] do
      if ys == 0 then break
      let y := low ys
      ys := dropLow ys
      let mut zs := ys
      for _ in [:13] do
        if zs == 0 then break
        let s := x ||| y ||| low zs
        zs := dropLow zs
        let ba := badA || gs.any (fun t => ca[s ||| t]!)
        let bb := badB || gs.any (fun t => cb[s ||| t]!)
        res := gather d (left ^^^ s) (gs.push s) ba bb res
    return res

def shared := Id.run do
  let mut v := #[]
  for r in [:16] do v := gather 5 (65535 ^^^ bit r) #[bit r] false false v
  return v

def records := (((include_str "four-square.txt").trim.splitOn "\n").toArray.map
  (fun l => (l.splitOn " ").toArray.map String.toNat!))

def edgeMask (e : Nat) := bit (e/16) ||| bit (e%16)
def mateOf (es : Array Nat) := Id.run do
  let mut m := Array.replicate 16 16
  for e in es do
    let x := e/16
    let y := e%16
    m := (m.set! x y).set! y x
  return m

def witnesses (m : Matching) := Id.run do
  let cls := closed m
  let mut freq := Array.replicate 65536 0
  for row in shared do
    if row.any (fun s => cls[s]!) then
      for s in row do freq := freq.modify s (·+1)
  return freq

/-- Counting cuts gives an upper bound on the overlap. A fourth matching can
close several of the recorded cuts in the same grouping. -/
def summedCuts (freq : Array Nat) (es : Array Nat) := Id.run do
  let masks := unions es
  let mut h := 0
  for t in cuts2 do h := h+freq[masks[t]!]!
  for t in cuts3 do h := h+freq[masks[t]!]!
  return h

def extend (m : Matching) (freq : Array Nat) (hit target depth left : Nat) (es : Array Nat) : Bool := Id.run do
  match depth with
  | 0 => return hit + tripleCount base es ≥ target + summedCuts freq es
  | d+1 =>
    let x := (low left).log2
    let mut ys := dropLow left
    for _ in [:15] do
      if ys == 0 then break
      let y := (low ys).log2
      ys := dropLow ys
      if square.1[x]! != y && square.2[x]! != y && m[x]! != y then
        let e := bit x ||| bit y
        if !extend m freq hit target d (left ^^^ e) (es.push e) then return false
    return true

def checkRow (l : Array Nat) := Id.run do
  let es := l.extract 4 12
  let m := mateOf es
  let hit := tripleCount base (es.map edgeMask)
  if hit != l[1]! then return false
  if hit ≥ 113020 then return true
  let e := l[3]!
  let x := e/16
  let y := e%16
  if !(x < y && y < 16 && square.1[x]! != y && square.2[x]! != y && m[x]! != y) then return false
  let mask := edgeMask e
  return extend m (witnesses m) hit 113020 7 (65535 ^^^ mask) #[mask]

def batch (start finish : Nat) := (records.extract start finish).all checkRow

def pt (x : Nat) := if x == 0 then 15 else if x == 15 then 0 else x
def permutations : Array (Array Nat) := Id.run do
  let mut ps := #[]
  for a in [:4] do for b in [:4] do for c in [:4] do for d in [:4] do
    let blocks := #[a,b,c,d]
    if blocks.toList.eraseDups.length != 4 then continue
    for flip in [:2] do for shifts in [:256] do
      let mut p := Array.replicate 16 0
      for x in [:16] do
        let t := pt x
        let i := t/4
        let j := t%4
        let m := (shifts >>> (2*i))%4
        let y := if m%2 == 0 then j else 5-j
        let y := (y+2*(m/2))%4
        let y := if flip == 0 then y else (4-y)%4
        p := p.set! x (pt (4*blocks[i]!+y))
      ps := ps.push p
  return ps

def validPerm (p : Array Nat) :=
  p.size == 16 && p.all (· < 16) && p.toList.eraseDups.length == 16 &&
    [false,true].any fun swap => (Array.range 16).all fun x =>
      p[square.1[x]!]! == (if swap then square.2 else square.1)[p[x]!]! &&
      p[square.2[x]!]! == (if swap then square.1 else square.2)[p[x]!]!

def stamp (p es : Array Nat) : UInt64 := Id.run do
  let mut key : UInt64 := 0
  for e in es do
    let x := p[e/16]!
    let y := p[e%16]!
    key := key ||| (y.toUInt64 <<< (4*x).toUInt64) ||| (x.toUInt64 <<< (4*y).toUInt64)
  return key

def orbit := Id.run do
  let mut seen : Std.HashSet UInt64 := ∅
  for l in records do
    let es := l.extract 4 12
    for p in permutations do seen := seen.insert (stamp p es)
  return seen

def visitAll (depth left : Nat) (key : UInt64) : Bool := Id.run do
  match depth with
  | 0 => return orbit.contains key
  | d+1 =>
    let x := (low left).log2
    let mut ys := dropLow left
    for _ in [:15] do
      if ys == 0 then break
      let y := (low ys).log2
      ys := dropLow ys
      if square.1[x]! != y && square.2[x]! != y then
        let v := key ||| (y.toUInt64 <<< (4*x).toUInt64) ||| (x.toUInt64 <<< (4*y).toUInt64)
        if !visitAll d (left ^^^ (bit x ||| bit y)) v then return false
    return true

def legitimate (l : Array Nat) :=
  let es := l.extract 4 12
  es.size == 8 && es.all (fun e => e/16 < e%16 && e%16 < 16 && e < 256 &&
    square.1[e/16]! != e%16 && square.2[e/16]! != e%16) &&
  (es.map edgeMask).foldl (· ||| ·) 0 == 65535

def allOrbits := shared.size == 553600 && records.size == 169 && records.all legitimate &&
  permutations.all validPerm && visitAll 8 65535 0
end SquarePair
