import NineEncoding
import Std.Tactic.BVDecide.LRAT.Checker
import Std.Tactic.BVDecide.LRAT.Parser

open Std.Sat Std.Tactic.BVDecide
namespace WildExact.Nine

def parseFormula (doc : String) : Except String (CNF Nat) := do
  let mut clauses := #[]
  for line in doc.splitOn "\n" do
    if line.isEmpty || line.startsWith "p " then continue
    let fields := (line.splitOn " ").filter (· != "")
    unless fields.getLast? == some "0" do throw "missing clause terminator"
    let mut clause := #[]
    for t in fields.dropLast do
      let some v := t.toInt? | throw "noninteger literal"
      if v=0 then throw "unexpected clause terminator"
      clause := clause.push (v.natAbs-1,decide (v>0))
    clauses := clauses.push clause.toList
  return clauses.toList

def formula := (parseFormula (include_str "nine.cnf")).toOption.getD []
def decodeGate (i : Nat) := gates[i]?.getD (.count [] 0)

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem same_clauses : formula.relabel decodeGate = rules.map clause := by native_decide
theorem valid_rules : rules.all admissible=true := by native_decide

/-- The SAT solver supplies the witness. The standard library proves the soundness of the check. -/
theorem impossible_of_trace (p : Array LRAT.IntAction) (accepted : LRAT.check p formula=true)
    (b : Family) (caps : Caps b) : ¬ Hits b := by
  intro hits
  have semantic : CNF.eval (value b) (rules.map clause)=true := by
    apply List.all_eq_true.mpr
    intro l mem
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp mem
    exact rule_sound b hits caps r (List.all_eq_true.mp valid_rules r hr)
  rw [←same_clauses,CNF.eval_relabel] at semantic
  have unsat := LRAT.check_sound p formula accepted (value b ∘ decodeGate)
  rw [unsat] at semantic
  contradiction

end WildExact.Nine
