import CycleData24

/-! Rational moment inequalities for a balanced twelve-cut of K24. -/
namespace WildSieve.TwentyFour
open WildSieve.Thirty (Signature leftFree triples prescribe factor completeSix internal anchorClosed labelClosed overlap pick otherMoment Relation)

def signatures (t : Nat) : List Signature := do
  let l := leftFree t
  let r := 18-l
  let a ← List.range 2
  let b ← List.range (4-2*a)
  let c ← List.range (4-2*a-b)
  let d := 3-2*a-b-c
  let f ← List.range ((3-b)/2+1)
  let g ← List.range (4-b-2*f)
  let h := 3-b-2*f-g
  guard (c+g ≤ l ∧ d+h ≤ r)
  let x ← List.range ((l-c-g)/2+1)
  let y := l-c-g-2*x
  guard (y ≤ r-d-h ∧ (r-d-h-y)%2=0)
  pure ⟨a,b,c,d,f,g,h,x,y,(r-d-h-y)/2⟩

inductive Column
  | hist (ll lr rr : Nat)
  | colors (i : Nat)
  | duplicates (i : Nat)
  | cycles (index : Nat)
  | tripleMoment (u : Nat)
  | defect
  | mean (t : Nat)
  | signature (t : Nat) (s : Signature)
deriving DecidableEq, Repr

def columns : List Column :=
  (do
    let a ← List.range 7
    let b ← List.range 17
    let c ← List.range 7
    pure (Column.hist a b c)) ++
  (List.range 7).map .colors ++ (List.range 4).map .duplicates ++ [.defect,.tripleMoment 9,.tripleMoment 12] ++ (List.range 21).map .cycles ++
  (List.range 3).map .mean ++ (List.range 3).flatMap (fun t => (signatures t).map (.signature t))

inductive Row
  | mass | colors | leftEdges | anchorColor
  | duplicateColors | duplicateEdges | duplicateClosing
  | mean (t : Nat) | distinct (t : Nat) | regionalColors (t : Nat)
  | edges (t k : Nat) | anchor (t : Nat) | closing (t i : Nat)
  | product (t i k : Nat) | other (t k : Nat) | complement | rightComplement
  | cycleMass | profile (i : Nat) | raw (u : Nat) | population (u b : Nat)
deriving DecidableEq, Repr

def first (t i : Nat) : ℚ :=
  (completeSix i (12-2*i) i t : ℚ)*factor 12 12 t

/-- Select six anchor edges according to the number of their ends on a marked six. -/
def duplicateWeight (t i : Nat) : ℚ :=
  let target := 6-3*t
  let choices := ((List.range (i+1)).map (fun a =>
    let b := target-2*a
    if 2*a ≤ target ∧ a+b ≤ 6 then
      i.choose a * (6-2*i).choose b * (6+i).choose (6-a-b)
    else 0)).sum
  (choices : ℚ) / (Nat.choose 12 6) * factor 12 12 t

def otherBill (t k : Nat) (s : Signature) : ℚ :=
  let l := leftFree t
  let r := 18-l
  let sideA := if t=2 then 1 else 0
  let sideB := if t=0 then 0 else 1
  (completeSix s.x s.y s.z k : ℚ)*factor l r k +
    overlap sideA 0 s.a s.c s.x l r k + overlap sideA 1 s.a s.d s.z l r k +
    overlap sideB 0 s.f s.g s.x l r k + overlap sideB 1 s.f s.h s.z l r k

def edgeTotal (t k : Nat) : Nat :=
  let l := leftFree t
  let r := 18-l
  match k with
  | 0 => 3 | 1 => 9 | 2 => 3*l | 3 => 3*r | 4 => 3
  | 5 => 3*l | 6 => 3*r | 7 => l.choose 2 | 8 => l*r | _ => r.choose 2

def lowPopulation (i : Nat) : ℚ := if i=6 then 1 else 0
def highPopulation : Nat → ℚ
  | 0 => 12 | 1 => 72/5 | 2 => 18 | 3 => 20 | 4 => 15 | 5 => 12 | _ => 11
def lowMean : Nat → ℚ
  | 0 => 18/385 | 1 => 144/1375 | _ => 18/385
def highMean : Nat → ℚ
  | 0 => 10/7 | 1 => 112/121 | _ => 10/7

def cornerX (i k : Nat) := if k=0 ∨ k=2 then lowPopulation i else highPopulation i
def cornerM (t k : Nat) := if k=0 ∨ k=3 then lowMean t else highMean t

def coeff : Row → Column → ℚ
  | .mass, .hist _ _ _ => 1
  | .colors, .colors _ => 1
  | .leftEdges, .colors i => i
  | .anchorColor, .colors i => if i=6 then 1 else 0
  | .duplicateColors, .duplicates _ => 1
  | .duplicateColors, .defect => -23
  | .duplicateEdges, .duplicates i => i
  | .duplicateEdges, .defect => -15
  | .duplicateClosing, .duplicates i => if i=3 then 1 else 0
  | .duplicateClosing, .defect => -2
  | .mean t, .hist a b c => pick a b c t
  | .mean t, .mean j => if t=j then -1 else 0
  | .distinct t, .mean j => if t=j then 1 else 0
  | .distinct t, .colors i => -first t i
  | .distinct t, .duplicates i => duplicateWeight t i / 23
  | .regionalColors t, .signature j _ => if t=j then 1 else 0
  | .regionalColors t, .mean j => if t=j then -23 else 0
  | .edges t k, .signature j s => if t=j then s.cell k else 0
  | .edges t k, .mean j => if t=j then -(edgeTotal t k : ℚ) else 0
  | .anchor t, .signature j s => if t=j ∧ anchorClosed s t then 1 else 0
  | .anchor t, .mean j => if t=j then -1 else 0
  | .closing t i, .signature j s => if t=j ∧ internal s t=i ∧ labelClosed s then 1 else 0
  | .closing t i, .colors j => if i=j then -first t i else 0
  | .product t i _, .signature j s => if t=j ∧ internal s t=i then 1 else 0
  | .product t i k, .mean j => if t=j then -cornerX i k else 0
  | .product t i k, .colors j => if i=j then -cornerM t k else 0
  | .other t k, .hist a b c => otherMoment a b c t k
  | .other t k, .signature j s => if t=j then -otherBill t k s else 0
  | .complement, .hist a b c => otherMoment a b c 0 0
  | .complement, .signature j s =>
      if j=0 then (if s.c+s.g+s.y=0 then 1 else 0)-otherBill 0 0 s else 0
  | .complement, .mean j => if j=0 then -1 else 0
  | .rightComplement, .hist a b c => otherMoment a b c 2 2
  | .rightComplement, .signature j s =>
      if j=2 then (if s.d+s.h+s.y=0 then 1 else 0)-otherBill 2 2 s else 0
  | .rightComplement, .mean j => if j=2 then -1 else 0
  | .cycleMass, .cycles _ => 1
  | .profile i, .colors j => if i=j then 1 else 0
  | .profile i, .cycles j => -((22*atCell j 12 6 i : Nat) : ℚ)/(Nat.choose 12 6 : ℚ)
  | .raw u, .tripleMoment v | .population u _, .tripleMoment v => if u=v then 1 else 0
  | .raw u, .cycles j => -(((if u=12 then 220 else 329)*pairCount j (12-u) : Nat) : ℚ)/(Nat.choose 24 u : ℚ)
  | .population u b, .cycles j =>
      -((b*pairCount j (12-u) : Nat)/(Nat.choose 24 u : ℚ)+polyMean j u b)
  | _, _ => 0

def rhs : Row → ℚ
  | .cycleMass => 1 | .profile i => if i=6 then 1 else 0
  | .mass => 1 | .colors => 23 | .leftEdges => 66 | .anchorColor => 1
  | .product t i k => -cornerX i k*cornerM t k
  | _ => 0

def sense : Row → Relation
  | .anchorColor | .duplicateClosing | .anchor _ => .ge
  | .product _ _ k => if k<2 then .ge else .le
  | .other _ _ | .complement | .rightComplement | .raw _ | .population _ _ => .le
  | _ => .eq

def prob (j : Nat) := prescribe 24 j
def wedgePrice : ℚ := 2/3-(1/3+13/126)*36*prob 4/prob 3
def lateMass : ℚ := (23*Nat.choose 12 6*(triples 4)^2 : Nat)/(2*(triples 8 : ℚ))

def objective : Column → ℚ
  | .hist 0 0 0 => lateMass
  | .defect => -10*prob 2+(9/14)*100*780*prob 4+wedgePrice*1000*prob 3
  | .tripleMoment u => if u=12 then (3/14)*Nat.choose 24 12*1000*prob 6/6
      else (13/42)*Nat.choose 24 9*10*prob 5/2
  | .cycles j => 5060*10*prob 2-(9/14)*50*(pairCount j 0)*prob 4-
      wedgePrice*(pairCount j 3)*prob 3/2
  | _ => 0

end WildSieve.TwentyFour
