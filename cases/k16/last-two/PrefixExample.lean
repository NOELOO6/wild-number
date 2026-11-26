import SearchExample
import Prescribed
namespace PrefixExample
open Prescribed

/-- Bits 0 and 1 mark the two outside colors, bit 2 marks any named color. -/
def walls := Id.run do
  let mut marks := Array.replicate 65536 0
  for (m,c) in SearchExample.rows.zipIdx do
    let colorBit := if c=0 then 1 else if c=4 then 2 else 4
    let mut unions := #[0]
    for x in [:16] do
      if x < m[x]! then unions := unions ++ unions.map (· ||| (bit x ||| bit m[x]!))
    for u in unions do marks := marks.modify u (· ||| colorBit)
  return marks
/-- Each base-2^25 digit counts a different outcome. There are fewer than
2^25 groupings across all roots, so the digits cannot carry. -/
def visit (depth left : Nat) (groups : Array Nat) (hit : Nat) : Nat := Id.run do
  match depth with
  | 0 => return 1 <<< (25*hit)
  | d+1 =>
    let x := low left
    let mut ys := dropLow left
    let mut result := 0
    for _ in [:14] do
      if ys == 0 then break
      let y := low ys
      ys := dropLow ys
      let mut zs := ys
      for _ in [:13] do
        if zs == 0 then break
        let t := x ||| y ||| low zs
        zs := dropLow zs
        let bad := groups.foldl (fun v s => v ||| walls[s ||| t]!) hit
        if bad < 4 then result := result + visit d (left ^^^ t) (groups.push t) bad
    return result

def totals := ((Array.range 16).map (fun r => visit 5 (65535 ^^^ bit r) #[bit r] 0)).toList.sum
theorem breakdown : SearchExample.valid = true ∧
    totals = 1731000 + 393550*2^25 + 393550*2^50 + 75521*2^75 := by native_decide
#print axioms breakdown
end PrefixExample
