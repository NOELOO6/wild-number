import CrossBoundary
namespace CrossBoundary
open SixBoundary

def originalBits := bits FixedSix.succeeds FixedSix.all

/-- Restrict the initial live bits to the original nineteen groupings. -/
def retain : List (List Row) → Nat → Nat → Bool
  | [], _, alive => enough 2 alive
  | pool::tail, used, alive => pool.all (fun r =>
    used &&& r.hidden != 0 || retain tail (used ||| r.hidden) (alive &&& r.wins))

end CrossBoundary
