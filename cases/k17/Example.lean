import Std
namespace K17Example

def groups : List (List Nat) := [[0,1,2,3,5],[4,6,9],[7,8,12],[10,11,15],[13,14,16]]
def path : List Nat → List (Nat × Nat)
  | a::b::xs => (a,b) :: path (b::xs)
  | _ => []
def wild := groups.flatMap path

/-- Color c pairs x with 2c-x modulo 17. The value x=c models an absent
    edge by a harmless stationary step. -/
def mate (c v : Nat) := (2*c+17-v)%17
def reachable (c : Nat) : Nat := Id.run do
  let mut seen := 1
  for _ in [:17] do
    for v in [:17] do
      if seen.testBit v then seen := seen ||| (1 <<< mate c v)
    for (u,v) in wild do
      if seen.testBit u || seen.testBit v then seen := seen ||| (1 <<< u) ||| (1 <<< v)
  return seen

theorem twelve_work : wild.length = 12 ∧ ∀ c : Fin 17, reachable c = 131071 := by native_decide
#print axioms twelve_work
end K17Example
