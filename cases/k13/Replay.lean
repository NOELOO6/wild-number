import Std.Tactic.BVDecide.LRAT.Checker
import Std.Tactic.BVDecide.LRAT.Parser

open Std.Sat
open Std.Tactic.BVDecide

/-- DIMACS numbers start at 1. The standard LRAT checker shifts Lean's
    zero-based variables back to the DIMACS convention internally. -/
def parseCNF (doc : String) : Except String (CNF Nat) := do
  let mut clauses := #[]
  for line in doc.splitOn "\n" do
    if line.isEmpty || line.startsWith "c" || line.startsWith "p" then continue
    let tokens := (line.splitOn " ").filter (fun s => !s.isEmpty)
    unless tokens.getLast? == some "0" do throw "missing clause terminator"
    let mut lits := #[]
    for t in tokens.dropLast do
      let some v := t.toInt? | throw "invalid integer"
      if v == 0 then throw "unexpected zero"
      lits := lits.push (v.natAbs - 1, decide (v > 0))
    clauses := clauses.push lits.toList
  return clauses.toList

def main (args : List String) : IO UInt32 := do
  let [formula, trace] := args | throw <| IO.userError "expected a CNF and an LRAT path"
  let f ← IO.ofExcept <| parseCNF (← IO.FS.readFile formula)
  let p ← LRAT.loadLRATProof trace
  if LRAT.check p f then
    IO.println s!"Lean LRAT checker accepted {f.length} clauses and {p.size} proof actions."
    return 0
  IO.eprintln "LRAT certificate rejected."
  return 1

#check LRAT.check_sound
