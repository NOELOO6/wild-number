import NineCertificate
open Std.Tactic.BVDecide
namespace WildExact.Nine

/-- Store binary LRAT bytes as ASCII hex for Lean 4.19's string-literal support. -/
def readHex (s : String) : ByteArray := Id.run do
  let src := s.toUTF8
  let val := fun (c : UInt8) => if c < 58 then c-48 else c-87
  let mut out := ByteArray.emptyWithCapacity (src.size / 2)
  for i in [:src.size / 2] do
    out := out.push ((val src[2*i]! <<< 4) ||| val src[2*i+1]!)
  return out

private def trace := (LRAT.parseLRATProof (readHex (include_str "nine.hex"))).toOption.getD #[]

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem nine_points (b : Family) (caps : Caps b) : ¬ Hits b :=
  impossible_of_trace trace (by native_decide) b caps

#print axioms nine_points
end WildExact.Nine
