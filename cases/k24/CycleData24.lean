import Concentration24

namespace WildSieve.TwentyFour

/-- All partitions of twelve into ascending parts of size at least two.
The parts count edges of each color on an alternating cycle. -/
def cycleLists : Nat → Nat → Nat → List (List Nat)
  | 0,_,total => if total=0 then [[]] else []
  | fuel+1,lo,total => if total=0 then [[]] else do
      let k ← List.range (total+1)
      guard (lo≤k)
      let rest ← cycleLists fuel k (total-k)
      pure (k::rest)

def shapes := cycleLists 6 2 12

/-- A cell counts subsets by their cardinality and their numbers of internally
paired edges in the two colors. Only sizes through twelve can enter the proof. -/
def cellIndex (u i j : Nat) := (u*7+i)*7+j
private def cells := 13*7*7

structure Entry where
  u : Nat
  i : Nat
  j : Nat
  count : Nat
deriving Inhabited, Repr

def entries (a : Array Nat) : Array Entry := Id.run do
  let mut out := #[]
  for u in [:13] do
    for i in [:7] do
      for j in [:7] do
        let w := a[cellIndex u i j]!
        if w>0 then out := out.push ⟨u,i,j,w⟩
  return out

/-- Transfer along one cycle, closing the last edge back to the first bit. -/
def oneCycle (len : Nat) : Array Entry := Id.run do
  let mut result := Array.replicate cells 0
  for first in [:2] do
    let mut a := (Array.replicate (2*cells) 0).set! (2*cellIndex first 0 0+first) 1
    for pos in [1:2*len] do
      let mut b := Array.replicate (2*cells) 0
      for idx in [:cells] do
        for last in [:2] do
          let w := a[2*idx+last]!
          if w>0 then
            let u := idx/49
            let i := idx/7%7
            let j := idx%7
            b := b.modify (2*idx) (·+w)
            let k := i+(pos%2)*last
            let l := j+((pos+1)%2)*last
            if u<12 && k<7 && l<7 then b := b.modify (2*cellIndex (u+1) k l+1) (·+w)
      a := b
    for idx in [:cells] do
      for last in [:2] do
        let j := idx%7+first*last
        if j<7 then result := result.modify (cellIndex (idx/49) (idx/7%7) j) (·+a[2*idx+last]!)
  return entries result

private def singleTables := (List.range 13).map oneCycle |>.toArray

def productTable (cs : List Nat) : Array Nat := Id.run do
  let mut result := (Array.replicate cells 0).set! 0 1
  for len in cs do
    let acc := entries result
    result := Array.replicate cells 0
    for a in acc do
      for b in singleTables[len]! do
        if a.u+b.u≤12 && a.i+b.i≤6 && a.j+b.j≤6 then
          result := result.modify (cellIndex (a.u+b.u) (a.i+b.i) (a.j+b.j)) (·+a.count*b.count)
  return result

def tables := (shapes.map productTable).toArray

def atCell (j u a b : Nat) := (tables[j]!)[cellIndex u a b]!

/-- For a fixed six-set with i pairs of the second color, choose three
edges of that color and count their endpoints in the six-set. -/
def companion (i r : Nat) :=
  ((List.range 4).map fun a =>
    let b := r-2*a
    if 2*a≤r ∧ a+b≤3 then i.choose a*(6-2*i).choose b*(6+i).choose (3-a-b) else 0).sum

def pairCount (j r : Nat) :=
  23*(220*companion 3 r+22*((List.range 4).map fun i => atCell j 6 3 i*companion i r).sum)

def featMean (j u : Nat) : List Nat → ℚ
  | [] => 1
  | [i] => (23*((List.range 7).map fun k => atCell j u i k).sum : Nat)/(uMass : ℚ)
  | i::k::_ => (23*22*atCell j u i k : Nat)/(uMass : ℚ)
where uMass := Nat.choose 24 u

def polyMean (j u b : Nat) : ℚ :=
  (((price u b).zip (features u)).map fun z => z.1*featMean j u z.2).sum

private theorem totals : shapes.length=21 ∧
    (List.range 21).all (fun j => [6,9,12].all (fun u =>
       ((List.range 7).map (fun i => ((List.range 7).map fun k => atCell j u i k).sum)).sum==
         Nat.choose 24 u))=true := by native_decide

end WildSieve.TwentyFour
