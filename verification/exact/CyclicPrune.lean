import CyclicScan

namespace WildExact.Rotation
open EdgeWalk
variable {n : Nat}

/-- A starter search whose excluded edges have already been ruled out by
the chosen cyclic coordinates. -/
def scanAllowed (allow : Fin n → Fin n → Bool) (test : List (Edge n) → Bool) :
    Nat → List (Fin n) → List Nat → List (Edge n) → Bool
  | _, [], _, es => test es
  | 0, _::_, _, _ => false
  | k+1,a::xs,used,es => xs.all fun b => !allow a b || dist a b∈used ||
      scanAllowed allow test k (xs.erase b) (dist a b::used) ((a,b)::es)

/-- The smallest partner of 1 obtained by scaling either endpoint by a unit. -/
def unitLimit (x y : Fin (n+1)) : Nat :=
  (List.finRange (n+1)).foldl (fun h u => min h (min (if u*x=1 then (u*y).val else n+1)
    (if u*y=1 then (u*x).val else n+1))) (n+1)

def unitLimits (n : Nat) := Array.ofFn fun x : Fin (n+1) => Array.ofFn fun y : Fin (n+1) => unitLimit x y

def allowedUnitEdge (limits : Array (Array Nat)) (t x y : Fin (n+1)) :=
  (x != 1 || y == t) && decide (t.val≤limits[x.val]![y.val]!)

end WildExact.Rotation
