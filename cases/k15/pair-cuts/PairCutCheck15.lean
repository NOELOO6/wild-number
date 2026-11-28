import Prescribed

namespace PairCutCheck15
open Prescribed
set_option maxRecDepth 200000

inductive Goal where | oneRoot | clearPairs | squarePairs | rootFours deriving Repr

structure Row where
  cycles : Array Nat
  thirds : Nat
  pairs : Array Int
  delta : Int
  gain : Int
  edges : Array Int
  transfer : Array Int
  deriving Inhabited

structure Prices where
  header : Array Int
  a : Array Int
  rows : Array Row
  deriving Inhabited

def prices (goal : Goal) : Prices := Id.run do
  let text := match goal with
    | .oneRoot => include_str "one-root-prices.txt"
    | .clearPairs => include_str "two-triples.txt"
    | .squarePairs => include_str "square-pairs.txt"
    | .rootFours => include_str "root-fours.txt"
  let ls := (text.trim.splitOn "\n").toArray.map fun l => (l.splitOn " ").toArray.map String.toInt!
  let rows := (Array.range 11).map fun i =>
    let pos := 2+4*i
    let h := ls[pos+1]!
    (⟨ls[pos]!.map Int.toNat,h[0]!.toNat,h.extract 1 4,h[4]!,h[5]!,ls[pos+2]!,ls[pos+3]!⟩ : Row)
  return ⟨ls[0]!,ls[1]!,rows⟩

def templates : Array (Array Nat) :=
  #[#[4,4,4,4],#[4,4,8],#[4,6,6],#[4,12],#[6,4,6],#[6,10],
    #[8,4,4],#[8,8],#[10,6],#[12,4],#[16]]

def chart := Id.run do
  let mut t := Array.replicate 6561 11
  for i in [:11] do t := t.set! (key templates[i]!.toList) i
  return t

-- Only masks not containing the singleton root are ranked in these two tables.
def tripleRank := rankOf (maskList 15 3)
def sixRank := rankOf (maskList 15 6)
@[inline] def splitId (q s t : Nat) := tripleRank[q ^^^ 32768]!*5005 + sixRank[min s t]!

structure Ledger where
  total : Nat
  one : Array Nat
  two : Array Int
  sides : Array Int
  splits : Array Int
  deriving Inhabited

def deposit (a : Array Int) (gs : Array Nat) (ma mb : Nat) (v : Ledger) : Ledger := Id.run do
  let one := v.one.modify ma (·+1)
  if ma == 0 || mb == 0 then return {v with total := v.total+1, one}
  let ra := if ma == 1 then 1 else 0
  let rb := if mb == 1 then 1 else 0
  let two := v.two.modify (ra+rb) (·+1)
  let wp := a[6+ra+2*rb]!
  let wr := a[10+ra+2*rb]!
  let mut sides := v.sides
  let mut splits := v.splits
  for i in [:5] do
    let q := gs[i]! ||| 32768
    sides := sides.modify q (·+wr)
    for j in [:i] do sides := sides.modify (gs[i]! ||| gs[j]!) (·+wp)
    let first := if i == 0 then 1 else 0
    for j in [first+1:5] do
      if j != i then
        let s := gs[first]! ||| gs[j]!
        splits := splits.modify (splitId q s (65535 ^^^ q ^^^ s)) (·-(wp+wr))
  return ⟨v.total+1,one,two,sides,splits⟩

@[inline] def nextMode (closed : Array Bool) (old s : Nat) (gs : Array Nat) :=
  if old == 2 || gs.any (fun t => closed[s ||| t]!) then 2
  else if old == 1 || closed[s ||| 32768]! then 1 else 0

def draw (a : Array Int) (ca cb : Array Bool) (depth left : Nat) (gs : Array Nat)
    (ma mb : Nat) (v : Ledger) : Ledger := Id.run do
  match depth with
  | 0 => return deposit a gs ma mb v
  | n+1 =>
    let x := low left
    let mut ys := dropLow left
    let mut result := v
    for _ in [:14] do
      if ys == 0 then break
      let y := low ys
      ys := dropLow ys
      let mut zs := ys
      for _ in [:13] do
        if zs == 0 then break
        let s := x ||| y ||| low zs
        zs := dropLow zs
        result := draw a ca cb n (left ^^^ s) (gs.push s)
          (nextMode ca ma s gs) (nextMode cb mb s gs) result
    return result

-- For a rooted four, the other six matching edges split into two threes in ten ways.
def ordinaryTriples := maskList 7 3
def complements := (Array.range 7).map fun i =>
  let rem := 127 ^^^ bit i
  (ordinaryTriples.filter fun s => s &&& rem == s && s &&& low rem != 0).map fun s => (s,rem ^^^ s)

def incidence (v : Ledger) (rootEdge : Nat) (es : Array Nat) : Int := Id.run do
  let sides := unions es
  let mut value : Int := 0
  for s in ordinaryTriples do value := value+v.sides[sides[s]!]!
  for i in [:7] do
    let q := rootEdge ||| es[i]!
    value := value+v.sides[q]!
    for (s,t) in complements[i]! do
      value := value+v.splits[splitId q sides[s]! sides[t]!]!
  return value

def third (row : Row) (v : Ledger) (a b : Matching) (depth left : Nat)
    (m es : Array Nat) (rootEdge : Nat) (charge : Int) : Nat := Id.run do
  match depth with
  | 0 =>
    let j := chart[typeKey true a m]!
    let k := chart[typeKey true b m]!
    if j >= 11 || k >= 11 then return 1000000000
    return if charge+row.transfer[11*j+k]! ≤ incidence v rootEdge es+row.delta then 1 else 1000000000
  | n+1 =>
    let x := (low left).log2
    let mut ys := dropLow left
    let mut count := 0
    for _ in [:15] do
      if ys == 0 then break
      let y := (low ys).log2
      ys := dropLow ys
      if a[x]! != y && b[x]! != y then
        let e := bit x ||| bit y
        let rooted := y == 15
        count := count+third row v a b n (left ^^^ e) ((m.set! x y).set! y x)
          (if rooted then es else es.push e) (if rooted then e else rootEdge) (charge+row.edges[pairId x y]!)
    return count

def checkRow (goal : Goal) (i : Nat) : Bool := Id.run do
  let c := prices goal
  let row := c.rows[i]!
  let (a,b) := canonical row.cycles
  let v := draw c.a (closed a) (closed b) 5 32767 #[] 0 0
    ⟨0,#[0,0,0],#[0,0,0],Array.replicate 65536 0,Array.replicate (455*5005) 0⟩
  let mut edge : Int := 0
  for y in [:16] do
    for x in [:y] do
      if a[x]! != y && b[x]! != y then edge := edge+row.edges[pairId x y]!
  let mut pair : Int := 0
  for j in [:3] do pair := pair+c.a[3+j]!*v.two[j]!
  return row.cycles == templates[i]! && v.total == 1401400 && v.one == #[1209600,100800,91000] &&
    v.two == row.pairs && 105*pair+35*(edge-13*row.delta) == row.gain &&
    row.thirds == (#[673601,673535,673504,673502,673504,673472,673535,673473,673472,673502,673471] : Array Nat)[i]! && third row v a b 8 65535 (Array.replicate 16 0) #[] 0 0 == row.thirds

end PairCutCheck15
