import OutsideNames
open Std.Tactic.BVDecide

def main (args : List String) : IO Unit := do
  let [file] := args | throw (IO.userError "expected a binary LRAT certificate")
  let proof ← IO.ofExcept (LRAT.parseLRATProof (← IO.FS.readBinFile file))
  unless (InsideNames.certifyOutside proof).isSome do throw (IO.userError "proof rejected")
  IO.println s!"Lean verified OutsideFixed using {proof.size} certificate steps."
