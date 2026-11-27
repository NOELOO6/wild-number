import QuartetTrap
namespace WildExact.Regroup.QuartetTrap
open WildDeletion

/-- A bit set records a side of a cut. Test closure directly against the
sixteen partners of the given color. -/
private def sealed (mask : Nat) (c : Fin 15) : Bool :=
  (List.finRange 16).all fun v => !mask.testBit v.val || mask.testBit (partner c v).val

private def forbidden : Array Bool :=
  (Array.range 65536).map fun mask => (List.finRange 15).any (sealed mask)

/-- Pick the first unused point, then its two partners in increasing order.
Each unordered partition of the unused points occurs on exactly one branch.
A new triple can complete a four-point cut with the root or a six-point cut
with any earlier triple. -/
private def countLayouts (root : Nat) (cuts : Array Bool) :
    Nat → List Nat → List Nat → Nat
  | _, [], _ => 1
  | 0, _::_, _ => 0
  | fuel+1, x::xs, previous =>
      (xs.map fun y => ((xs.filter (y<·)).map fun z =>
        let t := 2^x ||| 2^y ||| 2^z
        if cuts[root ||| t]! || previous.any (fun p => cuts[p ||| t]!) then 0
        else countLayouts root cuts fuel (xs.filter (fun v => v != y && v != z)) (t::previous)).sum).sum

def winners (root : Fin 16) :=
  countLayouts (2^root.val) forbidden 5 ((List.range 16).erase root.val) []

theorem count_by_root : (List.finRange 16).map winners =
    [113017,120037,127003,123590,122005,123455,124185,119111,
     119566,117457,123581,117028,120355,126824,118935,126044] := by native_decide

theorem full_count : ((List.finRange 16).map winners).sum=1942193 := by rw [count_by_root]; decide
#print axioms full_count
end WildExact.Regroup.QuartetTrap
