import BoundaryOptions
import Std.Tactic.BVDecide.LRAT.Checker
import Std.Tactic.BVDecide.LRAT.Parser

namespace RedrawModel
open VertexRedraw EdgeWalk WildDeletion Std.Sat
abbrev Clause := CNF.Clause Nat
def lock (x y : V) := x.val == 15 || y.val == 15 || (6 ≤ x.val && 6 ≤ y.val)
def optTable := colors.toArray.map fun c => (BoundaryOptions.possible lock c).toArray
def opts (c : C) := optTable[c.val]!
def row (c : C) (j : Nat) : R := (opts c)[j]?.getD []
def groups := (numbers (include_str "groups.txt")).toArray
def tags := (numbers (include_str "hints.txt")).toArray
def vars : Array (C × Nat) := ((numbers (include_str "blocker.vars")).map
  (fun ns => (Fin.ofNat' 15 ns[0]!,ns[1]!))).toArray
def info (i : Nat) := vars[i]?.getD (0,0)
def parseCNF (doc : String) : Except String (CNF Nat) := do
  let mut cs := #[]
  for line in doc.splitOn "\n" do
    if line.isEmpty || line.startsWith "c" || line.startsWith "p" then continue
    let ts := (line.splitOn " ").filter (!·.isEmpty)
    unless ts.getLast? == some "0" do throw "missing terminator"
    let mut lits := #[]
    for t in ts.dropLast do
      let some v := t.toInt? | throw "invalid integer"
      if v == 0 then throw "unexpected zero"
      lits := lits.push (v.natAbs-1, decide (v>0))
    cs := cs.push lits.toList
  return cs.toList
def formula := (parseCNF (include_str "blocker.cnf")).toOption.getD []

def hasEdge (m : R) (x y : V) := m.contains (x,y) || m.contains (y,x)
def onRows (c : C) (p : R → Bool) := SixBoundary.bits p (opts c).toList
def eMask (c : C) (x y : V) := onRows c (fun m => hasEdge m x y)
def wMask (c : C) (g : List Nat) := onRows c (fun m => passes 0 (trial g ++ erase m))
def ones (c : C) := 2^(opts c).size-1

/-- For a fixed color, which row choices already satisfy a clause? -/
def supports (c : C) : Clause → Nat
  | [] => 0
  | (i,pos)::tail =>
    let (d,s) := info i
    let head := if c==d then (if pos then s else ones c ^^^ s) else 0
    head ||| supports c tail

/-- The large lookups are evaluated once. -/
def edgeTable := (List.finRange 15).toArray.map fun c =>
  points.toArray.map fun x => points.toArray.map fun y => eMask c x y
def winTable := groups.map fun g => colors.toArray.map fun c => wMask c g
def em (c : C) (x y : V) := edgeTable[c.val]![x.val]![y.val]!
def wm (i : Nat) (c : C) := winTable[i]![c.val]!

/-- A clause follows locally, from covering an edge, from edge disjointness,
or from the assumption that a grouping loses. -/
def valid (cl : Clause) : List Nat → Bool
  | [0,d] => let c := Fin.ofNat' 15 d; (supports c cl &&& ones c) == ones c
  | [1,a,b] => let x := Fin.ofNat' 16 a; let y := Fin.ofNat' 16 b
    x != y && colors.all (fun c => (supports c cl &&& em c x y) == em c x y)
  | [2,a,b,d,h] => let x := Fin.ofNat' 16 a; let y := Fin.ofNat' 16 b
    let c := Fin.ofNat' 15 d; let k := Fin.ofNat' 15 h
    c != k && [c,k].all (fun j => ((supports j cl ||| em j x y) &&& ones j) == ones j)
  | [3,i] => decide (i < groups.size) && colors.all
      (fun c => ((supports c cl ||| wm i c) &&& ones c) == ones c)
  | _ => false

def census := (formula.zip tags.toList).all (fun p => valid p.1 p.2)
end RedrawModel
