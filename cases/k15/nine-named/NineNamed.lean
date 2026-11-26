import Prescribed
namespace NineNamed
open Prescribed
@[noinline] def parseInts (s : String) := ((s.trim.splitOn "\n").toArray.map
    (fun l => (l.splitOn " ").toArray.map String.toInt!))
def ints := parseInts (include_str "nine-prices.txt")
def coeff : Array Int := ints[0]!
def a (z : Nat) := coeff[z]!
def b (g : Nat) := coeff[2+g]!
def c (g z : Nat) := coeff[5+2*g+z]!
def minGain : Array Int := #[119975001749,-31157095571,-120008954672]
structure Row where
  cycles : Array Nat
  both : Nat
  offset : Array Int
  gain : Int
  prices : Array Int
  transfer : Array (Array (Array Int))
  deriving Inhabited

def rows : Array (Array Row) := (Array.range 3).map fun g => (Array.range 11).map fun i =>
  let pos := 1+25*(11*g+i)
  let h := ints[pos+1]!
  ⟨ints[pos]!.map Int.toNat,h[0]!.toNat,h.extract 1 3,h[3]!,ints[pos+2]!,
   #[ints.extract (pos+3) (pos+14),ints.extract (pos+14) (pos+25)]⟩

def go (i : Nat) (table : Array Nat) (rs : Array Row) (ct : Counts) (ma mb : Matching)
    (depth left : Nat) (m es : Array Nat) (p0 p1 p2 : Int) : Nat := Id.run do
  match depth with
  | 0 =>
    let j := table[typeKey true ma m]!
    let k := table[typeKey true mb m]!
    if j ≥ 11 || k ≥ 11 then return 1000000000
    let hit : Int := tripleCount ct es
    let ps := #[p0,p1,p2]
    for g in [:3] do
      let r := rs[g]!
      for z in [:2] do
        let f := r.transfer[z]!
        let fee := if g==1 then min f[j]![k]! f[k]![j]! else f[j]![k]!
        if -(c g z)*hit > ps[g]!+r.offset[z]!+fee then return 1000000000
    return 1
  | h+1 =>
    let x := (low left).log2
    let mut ys := dropLow left
    let mut ctAll := 0
    for _ in [:15] do
      if ys == 0 then break
      let y := (low ys).log2
      ys := dropLow ys
      if ma[x]! != y && mb[x]! != y then
        let e := bit x ||| bit y
        let id := pairId x y
        ctAll := ctAll + go i table rs ct ma mb h (left ^^^ e) ((m.set! x y).set! y x) (es.push e)
            (p0+rs[0]!.prices[id]!) (p1+rs[1]!.prices[id]!) (p2+rs[2]!.prices[id]!)
    return ctAll

def check (i : Nat) := Id.run do
  let rs := rows.map (·[i]!)
  let table := keyTable (read true)
  let cycles := rs[0]!.cycles
  if table[key cycles.toList]! != i then return false
  let (ma,mb) := canonical cycles
  let ct := counts true ma mb
  if ct.one != 191800 then return false
  for g in [:3] do
    let r := rs[g]!
    if r.cycles != cycles || ct.both != r.both then return false
    let mut bill : Int := 0
    for y in [:16] do for x in [:y] do
      if ma[x]! != y && mb[x]! != y then bill := bill+r.prices[pairId x y]!
    let gain := b g*(ct.both : Int)-bill-(7+g : Nat)*r.offset[0]!-(6-g : Nat)*r.offset[1]!
    if gain != r.gain || gain < minGain[g]! then return false
  return go i table rs ct ma mb 8 65535 (Array.replicate 16 0) #[] 0 0 0 == (expected true)[i]!

/-- x,y,z label the three colors as named (0) or other (1).
i,j,k are respectively the types of the first-second, first-third and
second-third color pairs. The mixed pair is billed named endpoint first. -/
def fee (x y z i j k : Nat) :=
  let f := rows[x+y]![i]!.transfer[z]!
  if x > y then f[k]![j]! else f[j]![k]!
def cancelled := (Array.range 2).all fun x => (Array.range 2).all fun y => (Array.range 2).all fun z =>
  (Array.range 11).all fun i => (Array.range 11).all fun j => (Array.range 11).all fun k =>
     fee x y z i j k + fee x z y j i k + fee y z x k i j ≤ 0 &&
     fee x y z i j k == fee y x z i k j

def pairs (x : Nat) := x*(x-1)/2
def term (x y g : Nat) : Int :=
  let p : Int := (#[pairs x,x*y,pairs y][g]! : Nat)
  p*(b g + c g 0*(x-(2-g) : Nat) + c g 1*(y-g : Nat))
def baseScore (x y : Nat) := 1000000 + a 0*x + a 1*y
def extraScore (x y : Nat) := term x y 0 + term x y 1 + term x y 2
def wins (x y : Nat) : Int := if x=0 ∧ y≤1 then 1 else 0
end NineNamed
