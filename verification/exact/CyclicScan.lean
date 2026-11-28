import EdgeWalk

namespace WildExact.Rotation
open EdgeWalk

variable {n : Nat}

def dist (a b : Fin n) := min (max a.val b.val - min a.val b.val)
  (n - (max a.val b.val - min a.val b.val))

/-- From the least unpaired point, try each partner of an unused circular length. -/
def scan (test : List (Edge n) → Bool) : Nat → List (Fin n) → List Nat → List (Edge n) → Bool
  | _, [], _, es => test es
  | 0, _::_, _, _ => false
  | fuel+1, a::rest, used, es => rest.all fun b =>
      dist a b ∈ used || scan test fuel (rest.erase b) (dist a b :: used) ((a,b)::es)

end WildExact.Rotation
