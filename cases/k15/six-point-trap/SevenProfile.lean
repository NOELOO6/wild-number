import FixedSix
import StarGeometry

namespace SevenProfile
open VertexRedraw ThreeStars

/-- The inside triples are 012 and 345. Relabeling the six marked points
gives any other initial split. -/
def layouts := FixedSix.endings.map fun b => Layout.mk 1 ([7,56] ++ b)
def indices := List.finRange 280
def atLayout (i : Fin 280) := layouts[i.val]!
def table := indices.foldl (fun (acc : Array Nat) i =>
  (sides (atLayout i)).foldl (fun a s => a.modify s (· ||| 2^i.val)) acc)
  (Array.replicate 65536 0)
def shadow (m : R) := (subsets m).foldl (fun n s => n ||| (table[s]?.getD 0)) 0

def badCount (s : Nat) := (indices.filter fun i => s.testBit i.val).length

def inside (s : Nat) (e : EdgeWalk.Edge 16) := s.testBit e.1.val && s.testBit e.2.val
def count (s : Nat) (m : R) := (m.filter (inside s)).length
def cap (root within cross : Nat) : Nat :=
  match root,within,cross with
  | 0,0,0 => 28
  | 1,0,0 => 10
  | 0,1,0 => 46
  | 0,0,1 => 20
  | 0,1,1 => 40
  | 0,2,0 => 88
  | 1,1,0 => 40
  | 0,0,2 => 40
  | 1,0,1 => 10
  | _,_,_ => 0

def cert (m : R) :=
  full m == 65535 && (if count 32831 m > 2 || count 32775 m == 2 || count 32824 m == 2 then true else
  let root := count 32831 m - count 63 m
  let within := count 7 m + count 56 m
  let cross := count 63 m - within
  decide (badCount (shadow m) ≤ cap root within cross))

/-- Generate a single complete matching at a time. The current prefix and
the remaining unpaired points suffice to check every possible color. -/
def visit (p : R → Bool) : Nat → List V → R → Bool
  | _, [], acc => p acc
  | 0, _::_, _ => false
  | d+1, x::xs, acc => xs.all fun y =>
    visit p d (xs.filter fun z => z != x && z != y) ((x,y)::acc)

def allColors := visit cert 16 points []
end SevenProfile
