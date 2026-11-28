import PairCutTable

namespace WildAnchor.K30
open Finset WildExact
set_option maxRecDepth 50000
set_option maxHeartbeats 0

def budget := (Nat.factorial 15*2^15-1)/28

/-- Cache the predecessor on each of the fifteen anchor edges before
enumerating two disjoint sets of three companion edges. -/
def fastPairBill (next : Equiv.Perm (Fin 15)) : Nat :=
  let prev := Array.ofFn fun i : Fin 15 => next.symm i
  ∑ k∈picks,reward (profile fun i => (code k i,code k prev[i.val]!))

def affordable (cs : List Nat) :=
  let single := singleBill cs
  decide (single≤budget) || decide (single≤budget+fastPairBill (cyclePerm 15 cs))

theorem sufficient : (cycleLists 15 3 15).all affordable=true := by native_decide

end WildAnchor.K30
