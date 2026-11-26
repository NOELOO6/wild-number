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

/-- Exact CNF from the supplied mathematical encoding. The error default is
    the satisfiable empty CNF, so a parse failure cannot establish this result. -/
def blockerFormula : CNF Nat :=
  (parseCNF (include_str "end38.cnf")).toOption.getD []

def blockerCertificate : Array LRAT.IntAction :=
  (LRAT.parseLRATProof (include_str "end38.lrat").toUTF8).toOption.getD #[]

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Native evaluation replays the LRAT proof. The standard library proves
    the checker's soundness. The compiler is in this theorem's trust base. -/
theorem cheap_start_obstruction_impossible : blockerFormula.Unsat := by
  exact LRAT.check_sound blockerCertificate blockerFormula (by native_decide)

#print axioms cheap_start_obstruction_impossible
