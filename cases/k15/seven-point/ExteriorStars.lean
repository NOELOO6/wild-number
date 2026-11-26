import ExteriorRows
namespace ExteriorRows
open VertexRedraw

def pricesAt (x : V) := colors.filter (fun c => !outside (SixBoundary.ref c x))
def nine : List V := [6,7,8,9,10,11,12,13,14]
def oldCount (c : C) := (nine.filter (fun x => outside (SixBoundary.ref c x) && x < SixBoundary.ref c x)).length
def required := colors.filter (fun c => oldCount c == 1)
def hints := ((include_str "exterior-repairs.txt").trim.splitOn "\n").toArray.map String.toNat!

structure Stats where
  visited : Nat := 0
  rescued : Nat := 0
  atTen : Nat := 0
  atEleven : Nat := 0
  atTwelve : Nat := 0
  errors : Nat := 0
  lastCode : Nat := 0
  deriving Repr, DecidableEq, Inhabited

/-- At each leaf the nine chosen missing colors are distinct. Each color
with only one exterior edge must be assigned to one of the nine points. -/
def scan : List V → Nat → Array Nat → Nat → Stats → Stats
  | [], used, t, code, s =>
    if required.all (fun c => used.testBit c.val) then
      let witness := hints[s.visited]?.getD 281
      let cost := if witness>0 && witness≤280 then
        budget (fun c => t[c.val]!) (Fin.ofNat' 280 (witness-1)) else 13
      ⟨s.visited+1,s.rescued+(if cost<10 then 1 else 0),
        s.atTen+(if cost=10 then 1 else 0),s.atEleven+(if cost=11 then 1 else 0),
        s.atTwelve+(if cost=12 then 1 else 0),
        s.errors+(if s.lastCode<code+1 && cost≤12 then 0 else 1),code+1⟩
    else s
  | x::xs, used, t, code, s => (pricesAt x).foldl (fun a c =>
    if used.testBit c.val then a else
    scan xs (used ||| 2^c.val) (t.set! c.val (key x)) (16*code+c.val) a) s

def starCensus := scan nine 0 (Array.replicate 15 0) 0 {}
end ExteriorRows
