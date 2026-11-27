import NineData

namespace WildExact.K13
open WildExact
abbrev V := Fin 13

/-- Bits 0 through 8 represent the nine points outside the selected four. -/
def remainder (i : Fin 14) : Nat := if 4≤i.val && i.val<13 then 1 <<< (i.val-4) else 0

def blockedMasks (r : Row 13) : List Nat := Id.run do
  let internal := r.filterMap fun (a,b) =>
    if remainder a != 0 && remainder b != 0 then some (remainder a ||| remainder b) else none
  let roots := r.filterMap fun (a,b) =>
    if a.val=13 && remainder b != 0 then some (remainder b) else
    if b.val=13 && remainder a != 0 then some (remainder a) else none
  let first := roots.flatMap fun x => internal.map (fun y => x ||| y)
  let second := (chooseK 3 internal).map fun es => 511 ^^^ es.foldl (· ||| ·) 0
  return first++second

def indices := ((List.range 512).map Nine.triples.idxOf).toArray
def blocked (r : Row 13) := (blockedMasks r).map (fun m => indices[m]?.getD 84)

structure Cap where
  subset : Nat
  threshold : Nat
  maximum : Nat
  deriving DecidableEq

def allCaps : List Cap := ⟨511,0,35⟩ :: (List.range 512).flatMap fun s =>
    ([(1,1,23),(4,2,30),(7,3,33)] : List (Nat × Nat × Nat)).filterMap fun (k,t,b) =>
      if Nine.bits s=k then some ⟨s,t,b⟩ else none

def capList (k : Cap) := Nine.ids.filter fun i => Nine.bits (Nine.mask i &&& k.subset) ≥ k.threshold
def coefficients (k : Cap) : List (Price 13) := Id.run do
  let d : List (Fin 14) := [0,1,2,3]
  let inside : List (Fin 14) := ((List.finRange 14).filter (fun a => remainder a &&& k.subset != 0))
  let rest : List (Fin 14) := (List.finRange 14).filter fun a => remainder a != 0
  let pairs (xs : List (Fin 14)) (v : Int) := xs.flatMap fun a =>
    ((xs.filter (a < ·)).map fun b => ((a,b),v))
  let root (xs : List (Fin 14)) (v : Int) := xs.map fun a => ((a,Fin.last 13),v)
  if k.threshold=0 then return pairs d 2 ++ root d (-1)
  let extra := if k.threshold=1 then
    inside.flatMap (fun a => (rest.filter (· != a)).map fun b => ((a,b),1))
    else if k.threshold=2 then pairs inside 1 else []
  return pairs d 1 ++ root d 1 ++ root inside 3 ++ extra

def base (k : Cap) : Int := if k.threshold=0 then 2 else 0
def factor (k : Cap) : Int := if k.threshold=0 then 1 else 2

def repeatPair (r : Row 13) := Four.paired (Four.ordinary r) 0 1 2 3
def penalty (r : Row 13) := Four.score (Four.ordinary r) (Four.star r) 0 1 2 3

/-- Precompute the two lookups for each cap once for all 135,135 matchings. -/
structure Budget where
  spec : Cap
  selected : Array Bool
  charges : List (Price 13)

def budgetFor (k : Cap) : Budget :=
  ⟨k,((List.range 85).map (fun i => (capList k).contains i)).toArray,coefficients k⟩
def budgets := allCaps.map budgetFor

def fastCheck : Bool := (Rows 13).all fun r => repeatPair r || Id.run do
  let bad := blocked r
  let penaltyValue := penalty r
  let table := Vector.ofFn (n:=14) fun a => Vector.ofFn (n:=14) fun b => rowHas r (a,b)
  return budgets.all fun y =>
    let occ := (bad.filter (fun i => y.selected[i]?.getD false)).length
    let cost := totalI y.charges fun ⟨(a,b),v⟩ => if (table.get a).get b then v else 0
    decide ((occ : Int) ≤ base y.spec + cost + factor y.spec * penaltyValue)

structure Grouping where
  a : Nat
  b : Nat
  c : Nat
  lines : TestLines 13

def vertices (i : Nat) := ((List.range 9).filter (Nine.mask i).testBit).map (·+4)
def grouping (a b c : Nat) : Grouping :=
  ⟨a,b,c,chains [[0,1,2,3],vertices a,vertices b,vertices c]⟩

def layouts := Nine.ids.flatMap fun a => Nine.ids.flatMap fun b =>
  (Nine.ids.filter (Nine.hit a b ·)).map (grouping a b)

def pathCheck : Bool := (Rows 13).all fun r => repeatPair r || Id.run do
  let bad := blocked r
  let colored := eraseRoot r
  return layouts.all fun w => bad.contains w.a || bad.contains w.b || bad.contains w.c ||
    EdgeWalk.passes 0 (w.lines ++ colored)

end WildExact.K13
