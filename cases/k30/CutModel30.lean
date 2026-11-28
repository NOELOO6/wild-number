import Mathlib.Data.Rat.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! Exact moment constraints for a random closed twelve-set in K30. -/
namespace WildSieve.Thirty

/-- Edge counts in the upper triangle on two distinguished triples and the unused
vertices on the two sides. -/
structure Signature where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  f : Nat
  g : Nat
  h : Nat
  x : Nat
  y : Nat
  z : Nat
deriving DecidableEq, Repr

def Signature.cell (s : Signature) : Nat → Nat
  | 0 => s.a | 1 => s.b | 2 => s.c | 3 => s.d | 4 => s.f
  | 5 => s.g | 6 => s.h | 7 => s.x | 8 => s.y | _ => s.z

def leftFree (t : Nat) := 6 + 3*t

def signatures (t : Nat) : List Signature := do
  let l := leftFree t
  let r := 24-l
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
  | defect
  | mean (t : Nat)
  | signature (t : Nat) (s : Signature)
deriving DecidableEq, Repr

def columns : List Column :=
  (do
    let a ← List.range 7
    let b ← List.range 25
    let c ← List.range 16
    pure (Column.hist a b c)) ++
  (List.range 7).map .colors ++ (List.range 4).map .duplicates ++ [.defect] ++
  (List.range 3).map .mean ++ (List.range 3).flatMap (fun t => (signatures t).map (.signature t))

inductive Row
  | mass | colors | leftEdges | anchorColor
  | duplicateColors | duplicateEdges | duplicateClosing
  | mean (t : Nat) | distinct (t : Nat) | regionalColors (t : Nat)
  | edges (t k : Nat) | anchor (t : Nat) | closing (t i : Nat)
  | product (t i k : Nat) | other (t k : Nat) | complement
deriving DecidableEq, Repr

def triples (n : Nat) := (3*n).factorial / (6^n*n.factorial)

def prescribe (points blocks : Nat) : ℚ :=
  (triples (points/3-blocks) : ℚ) / triples (points/3)

def factor (l r t : Nat) : ℚ :=
  match t with
  | 0 => 10*prescribe l 2
  | 1 => prescribe l 1*prescribe r 1
  | _ => 10*prescribe r 2

def completeSix (x y z : Nat) : Nat → Nat
  | 0 => x.choose 3
  | 1 => y.choose 3+x*y*z
  | _ => z.choose 3

def first (t i : Nat) : ℚ :=
  (completeSix i (12-2*i) (i+3) t : ℚ)*factor 12 18 t

/-- Select six anchor edges according to the number of their ends on a marked six. -/
def duplicateWeight (t i : Nat) : ℚ :=
  let target := 6-3*t
  let choices := ((List.range (i+1)).map (fun a =>
    let b := target-2*a
    if 2*a ≤ target ∧ a+b ≤ 6 then
      i.choose a * (6-2*i).choose b * (9+i).choose (6-a-b)
    else 0)).sum
  (choices : ℚ) / (Nat.choose 15 6) * factor 12 18 t

def internal (s : Signature) : Nat → Nat
  | 0 => s.a+s.b+s.c+s.f+s.g+s.x
  | 1 => s.a+s.c+s.x
  | _ => s.x

def anchorClosed (s : Signature) : Nat → Bool
  | 0 => s.d+s.h+s.y==0
  | 1 => s.b+s.d+s.g+s.y==0
  | _ => s.c+s.g+s.y==0

def labelClosed (s : Signature) := s.c+s.d+s.g+s.h==0

def overlap (side region internalPairs forced pairs : Nat) (l r k : Nat) : ℚ :=
  if side+region=k then
    let choices := if internalPairs=0 then (if forced=3 then 1 else 0)
      else (if forced=1 then pairs else 0)
    (choices : ℚ)*prescribe (if region=0 then l else r) 1
  else 0

def otherBill (t k : Nat) (s : Signature) : ℚ :=
  let l := leftFree t
  let r := 24-l
  let sideA := if t=2 then 1 else 0
  let sideB := if t=0 then 0 else 1
  (completeSix s.x s.y s.z k : ℚ)*factor l r k +
    overlap sideA 0 s.a s.c s.x l r k + overlap sideA 1 s.a s.d s.z l r k +
    overlap sideB 0 s.f s.g s.x l r k + overlap sideB 1 s.f s.h s.z l r k

def edgeTotal (t k : Nat) : Nat :=
  let l := leftFree t
  let r := 24-l
  match k with
  | 0 => 3 | 1 => 9 | 2 => 3*l | 3 => 3*r | 4 => 3
  | 5 => 3*l | 6 => 3*r | 7 => l.choose 2 | 8 => l*r | _ => r.choose 2

def lowPopulation (i : Nat) : ℚ := if i=6 then 1 else 0
def highPopulation : Nat → ℚ
  | 0 => 18 | 1 => 108/5 | 2 => 27 | 3 => 20 | 4 => 15 | 5 => 12 | _ => 11
def lowMean : Nat → ℚ
  | 0 => 12/385 | 1 => 432/4675 | _ => 101/1547
def highMean : Nat → ℚ
  | 0 => 10/7 | 1 => 115/187 | _ => 2355/3094

def cornerX (i k : Nat) := if k=0 ∨ k=2 then lowPopulation i else highPopulation i
def cornerM (t k : Nat) := if k=0 ∨ k=3 then lowMean t else highMean t

def pick (a b c : Nat) : Nat → Nat
  | 0 => a | 1 => b | _ => c

def otherMoment (a b c t k : Nat) : ℚ :=
  (pick a b c t * (pick a b c k - (if t=k then 1 else 0)) : Nat)

def coeff : Row → Column → ℚ
  | .mass, .hist _ _ _ => 1
  | .colors, .colors _ => 1
  | .leftEdges, .colors i => i
  | .anchorColor, .colors i => if i=6 then 1 else 0
  | .duplicateColors, .duplicates _ => 1
  | .duplicateColors, .defect => -29
  | .duplicateEdges, .duplicates i => i
  | .duplicateEdges, .defect => -15
  | .duplicateClosing, .duplicates i => if i=3 then 1 else 0
  | .duplicateClosing, .defect => -2
  | .mean t, .hist a b c => pick a b c t
  | .mean t, .mean j => if t=j then -1 else 0
  | .distinct t, .mean j => if t=j then 1 else 0
  | .distinct t, .colors i => -first t i
  | .distinct t, .duplicates i => duplicateWeight t i / 29
  | .regionalColors t, .signature j _ => if t=j then 1 else 0
  | .regionalColors t, .mean j => if t=j then -29 else 0
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
  | _, _ => 0

def rhs : Row → ℚ
  | .mass => 1 | .colors => 29 | .leftEdges => 66 | .anchorColor => 1
  | .product t i k => -cornerX i k*cornerM t k
  | _ => 0

inductive Relation | eq | le | ge
deriving DecidableEq

def sense : Row → Relation
  | .anchorColor | .duplicateClosing | .anchor _ => .ge
  | .product _ _ k => if k<2 then .ge else .le
  | .other _ _ | .complement => .le
  | _ => .eq

def objective : Column → ℚ
  | .hist 0 0 0 => 1
  | .defect => -1/18000
  | _ => 0

end WildSieve.Thirty
