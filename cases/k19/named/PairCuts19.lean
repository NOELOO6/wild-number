import Std
namespace PairCuts19
set_option maxRecDepth 20000

def factorial : Nat → Nat | 0 => 1 | n+1 => (n+1)*factorial n
def choose (n k : Nat) := if k>n then 0 else factorial n / (factorial k*factorial (n-k))
def choices := (Array.range 10).map fun n => (Array.range 10).map (choose n)
def types : Array (Array Nat) :=
  #[#[4,4,4,4,4],#[4,4,4,8],#[4,4,6,6],#[4,4,12],#[4,6,10],#[4,8,8],#[4,16],
    #[6,4,4,6],#[6,4,10],#[6,6,8],#[6,14],#[8,4,4,4],#[8,4,8],#[8,6,6],#[8,12],
    #[10,4,6],#[10,10],#[12,4,4],#[12,8],#[14,6],#[16,4],#[20]]
def digits (n k : Nat) := (Array.range 6).map fun i => (n/k^i)%k
def patterns (k : Nat) := ((Array.range (k^6)).map (digits · k)).filter fun a =>
  (a.toList.eraseDups == List.range k)
abbrev Cell := Nat × Nat
structure Shape where
  cells : List Cell
  leftSize : Nat
  orderings : Nat
  deriving Inhabited
/-- Each binary side excludes the group of four, so it is counted once. The
other partition labels its parts in order of first occurrence. -/
def shapes (k : Nat) := Id.run do
  let mut out : Array Shape := #[]
  for a in patterns k do for mask in [1:32] do
    let mut cells : Array Cell := Array.replicate k (0,0)
    for i in [:6] do
      let n := if i==5 then 4 else 3
      cells := cells.modify a[i]! (fun (x,y) => if mask.testBit i then (x+n,y) else (x,y+n))
    let mult := cells.foldl (fun w (x,y) => w*factorial x*factorial y) 1
    out := out.push ⟨cells.toList,(cells.map Prod.fst).toList.sum,mult⟩
  return out

def pt (x : Nat) := if x==0 then 0 else 1 <<< x
def pairUnits (cs : Array Nat) := Id.run do
  let mut a := #[]
  let mut b := #[]
  let mut start := 0
  for size in cs do
    for j in [:size/2] do
      let x := pt (start+2*j)
      let y := pt (start+2*j+1)
      let z := pt (start+(2*j+2)%size)
      a := a.push (x ||| y)
      b := b.push (y ||| z)
    start := start+size
  return (a,b)
def unions (es : Array Nat) := es.foldl (fun a e => a ++ a.map (· ||| e)) #[0]
/-- The signature of a binary side tells where the first color's unmatched
vertex lies and how many of its nine pairs lie inside or cross the side. -/
def counts (a b : Array Nat) := Id.run do
  let mut ct := Array.replicate 200 0
  for side in unions b do
    let mut one := 0
    let mut inside := 0
    let mut cross := 0
    for e in a do
      if e &&& (e-1) == 0 then one := (e &&& side != 0).toNat
      else if e &&& side == e then inside := inside+1
      else if e &&& side != 0 then cross := cross+1
    ct := ct.modify (100*one+10*inside+cross) (·+1)
  return ct

/-- Distribute the three classes of *distinguishable* pairs among cells,
then multiply by the number of within-cell orders. -/
def assign : List Cell → Nat → Nat → Nat → Nat
  | [], i,o,c => if i+o+c==0 then 1 else 0
  | (x,y)::rs,i,o,c => Id.run do
    let mut s := 0
    for z in [:min c (min x y)+1] do
      let u := (x-z)/2
      let v := (y-z)/2
      if 2*u+z==x && 2*v+z==y && u≤i && v≤o then
        s := s+choices[i]![u]!*choices[o]![v]!*choices[c]![z]!*assign rs (i-u) (o-v) (c-z)
    return s

def fill (cells : List Cell) (one inside outside cross : Nat) := Id.run do
  let mut n := 0
  for h in [:cells.length] do
    let (x,y) := cells[h]!
    if one≤x && 1-one≤y then
      n := n+assign (cells.set h (x-one,y-(1-one))) inside outside cross
  return n

def total (k : Nat) (cs : Array Nat) := Id.run do
  let mut res := 0
  for h in shapes k do
    for key in [:200] do
      let weight := cs[key]!
      if weight==0 then continue
      let one := key/100
      let i := (key/10)%10
      let c := key%10
      if one+2*i+c == h.leftSize then
        res := res+weight*h.orderings*fill h.cells one i (9-i-c) c
  return res
def repeats := factorial 4*(factorial 3)^5*factorial 5
def audit (i : Nat) := Id.run do
  let (a,b) := pairUnits types[i]!
  let ct := counts a b
  let flip := counts b a
  if flip != ct then return false
  let xx := total 2 ct
  let yx := total 3 ct
  return xx ≥ 50380208*repeats + 4*yx && xx ≥ 52111724*repeats + 3*yx
end PairCuts19
