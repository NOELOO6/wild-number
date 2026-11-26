import LossTree
namespace RawMenu
def pointKey (v : Fin 19) := 1 <<< v.val
def all := 524287
def popTable : Array Nat := Id.run do
  let mut t := #[0]
  for i in [1:524288] do t := t.push (t[i/2]!+i%2)
  return t
def bound : Nat → Nat
  | 3 => 214281 | 4 => 10716 | 6 => 14106 | 7 => 3723 | 9 => 3996 | _ => 0

def build : Array Nat := Id.run do
  let mut h := Array.replicate 524288 0
  for line in (include_str "layout-weights.txt").trim.splitOn "\n" do
    let entries := line.splitOn " "
    let w := entries.head!.toNat!
    let labels := entries[1]!.toList.toArray.map (fun x => x.toNat-'0'.toNat)
    for s in [1:32] do
      let mut m := 0
      for x in [:19] do
        if s.testBit labels[x]! then m := m ||| (1 <<< x)
      if popTable[m]! > 9 then m := m ^^^ all
      for a in [1:19] do
        let mut t := 0
        for x in [:19] do
          if m.testBit x then t := t ||| (1 <<< ((a*x)%19))
        for _ in [:19] do
          h := h.modify t (·+w)
          t := ((t <<< 1) &&& all) ||| (t >>> 18)
  return h

def losses := build.zipWith (fun n k => bound k - n) popTable
@[inline] def lost (s : Nat) : Nat := losses[s]?.getD 0
def run (v : Fin 19) := WildLoss.check lost pointKey 40695 9
  ((List.finRange 19).erase v) [0,pointKey v]
end RawMenu
