import SwitchFamily
import Lean.Data.Json

namespace WildExact.SwitchFamily
open Lean
set_option maxRecDepth 100000

structure Family where
  n : Nat
  exponent : Nat
  groups : List (List Nat)
  pairs : List (List Nat)
  deriving FromJson, Inhabited

def families : Array Family := ((include_str "families.jsonl").trim.splitOn "\n").toArray.map fun line =>
  ((Json.parse line >>= fromJson?).toOption.getD default)

abbrev Partners := Array (Array Nat)
private def put (p : Partners) (c x y : Nat) :=
  p.modify c fun row => (row.set! x y).set! y x

/-- The starting one-factorization on two equal layers. -/
def partners (m : Nat) : Partners := Id.run do
  let mut p := Array.replicate (2*m-1) (Array.replicate (2*m) (2*m))
  let ring := if m%2==1 then m else m-1
  let twist (v : Nat) := if m%2==1 && v%2==0 then m-1-v else v
  for c in [:ring] do
    for layer in [:2] do
      let center := (c+layer)%ring
      let center := if layer==1 then twist center else center
      for j in [1:ring/2+1] do
        let x := (center+j)%ring
        let y := (center+ring-j)%ring
        let x := if layer==1 then twist x else x
        let y := if layer==1 then twist y else y
        p := put p c (layer*m+x) (layer*m+y)
      if m%2==0 then p := put p c (layer*m+(c+layer)%ring) (layer*m+m-1)
    if m%2==1 then p := put p c c (m+(c+1)%m)
  for d in [:m] do
    if !(m%2==1 && d==1) then
      let c := ring+d-(if m%2==1 && d>1 then 1 else 0)
      for x in [:m] do p := put p c x (m+(x+d)%m)
  return p

abbrev RawChoice := List (Nat × Nat) × List (Nat × Nat)

/-- Separate the two alternating matchings on each connected cycle. -/
def cycleMenu (p : Partners) (a b : Nat) : List RawChoice := Id.run do
  let n := p.size+1
  let mut seen := Array.replicate n false
  let mut result := []
  for start in [:n] do
    if !seen[start]! then
      let mut x := start
      let mut left := []
      let mut right := []
      for step in [:n] do
        seen := seen.set! x true
        let y := p[if step%2==0 then a else b]![x]!
        if step%2==0 then left := (x,y)::left else right := (x,y)::right
        x := y
        if x==start then break
      result := (left,right)::result
  return result.reverse

def menus (d : Family) (p : Partners) : Array (List RawChoice) := Id.run do
  let mut choices := (Array.range d.n).map fun c =>
    let es := ((List.range (d.n+1)).filter fun v => v<p[c]![v]!).map fun v => (v,p[c]![v]!)
    [(es,es)]
  for pair in d.pairs do
    let a := pair[0]!
    let b := pair[1]!
    let cs := cycleMenu p a b
    choices := (choices.set! a cs).set! b cs
  return choices

/-- Discard edges at the extra singleton when testing the odd order. -/
def points (v : Nat) (es : List (Nat × Nat)) : List (Edge v) := es.filterMap fun (x,y) =>
  if hx : x<v then if hy : y<v then
    let a : Fin v := ⟨x,hx⟩
    let b : Fin v := ⟨y,hy⟩
    some (min a b,max a b)
  else none else none

def scheme (d : Family) (v : Nat) : Scheme v d.n :=
  let data := menus d (partners ((d.n+1)/2))
  let forest := d.groups.flatMap fun block => block.tail.map fun x => (block.head!,x)
  ⟨points v forest,fun c => (data[c.val]!).map fun (l,r) => (points v l,points v r)⟩

def dataOK (d : Family) : Bool := Id.run do
  let p := partners ((d.n+1)/2)
  let v := d.n+1
  if d.n%2 != 1 || p.size != d.n || d.groups.flatten.mergeSort (· ≤ ·)  !=  List.range d.n then return false
  for i in [:v] do
    let images := (List.range d.n).map fun c => p[c]![i]!
    if images.mergeSort (· ≤ ·)  !=  (List.range v).erase i then return false
    for c in [:d.n] do
      if p[c]![p[c]![i]!]!  !=  i then return false
  let mut exp := 0
  let mut used := []
  for ab in d.pairs do
    if ab.length  !=  2 then return false
    let a := ab[0]!
    let b := ab[1]!
    if a>=b || b>=d.n || used.contains a || used.contains b then return false
    used := a::b::used
    let cs := cycleMenu p a b
    if cs.any (fun (l,r) => l.length  !=  r.length || l.length<2) then return false
    exp := exp+(cs.length-1)
  return exp==d.exponent

def checkSize (d : Family) (v : Nat) : Bool :=
  if h : 0<v then
    letI : NeZero v := ⟨Nat.ne_of_gt h⟩
    checked (scheme d v) ((2*d.n+2)/3)
  else false

end WildExact.SwitchFamily
