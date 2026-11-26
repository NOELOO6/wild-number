import Teams
/- Three teams of five, with an extra root at point 0. Normalize T and U
   to be the first three points of A and B. The two points outside U in B
   distinguish the first and second groups. -/
namespace ThreeTeams
open Teams
set_option maxHeartbeats 0
set_option maxRecDepth 150000
def team (i : Nat) := List.range' (1+5*i) 5
def span (xs : List Nat) := xs.foldl (fun s x => s ||| bit x) 0
def t := [1,2,3]
def u := [6,7,8]
def layouts := t.flatMap fun single => u.flatMap fun b =>
  (team 2).flatMap fun c =>
    unorderedPairs ((team 2).erase c) fun x y =>
      [bit 9 ||| pair x y,
       bit 10 ||| span ((((team 2).erase c).erase x).erase y),
       bit single ||| span (u.erase b),
       pair 4 5 ||| bit c,
       span (t.erase single) ||| bit b]
def table := layouts.foldl (fun (z : Array Nat) g =>
  (cuts g).foldl (fun a s => a.modify s (·+1)) z) (Array.replicate 65536 0)
def cost (m : Matching) := total (closedSides m) (fun s => table[s]!)
def internal (i h : Nat) := (matchings 2 ((team i).erase h)).map (pair 0 h :: ·)
def external (i : Nat) := bijections (team ((i+1)%3)) (team ((i+2)%3))
def maxCost (i : Nat) (m : Matching) := ((external i).map (fun e => cost (m++e))).foldl max 0
def uses (m : Matching) (a b : Nat) := if pair a b ∈ m then 1 else 0
def upperA (m : Matching) := 18*(uses m 1 2+uses m 1 3+uses m 2 3)+
  18*(uses m 0 1+uses m 0 2+uses m 0 3)
def upperB (m : Matching) := 9*total u (fun x => uses m x 9 + uses m x 10)
def separate (p : Matching) := !(p.all fun e =>
  ((e &&& span t != 0) == (e &&& span u != 0)))
theorem candidates : layouts.length = 270 ∧ layouts.Nodup ∧ layouts.all genuine = true := by native_decide
theorem costA : (team 0).all (fun h => (internal 0 h).all
    (fun m => maxCost 0 m ≤ upperA m)) = true := by native_decide
theorem costB : (team 1).all (fun h => (internal 1 h).all
    (fun m => maxCost 1 m ≤ upperB m)) = true := by native_decide
theorem costC : (team 2).all (fun h => (internal 2 h).all (fun m =>
    (external 2).all (fun e => !separate e || cost (m++e) ≤ 12))) = true := by native_decide
theorem surviving (bad good : Nat) (n : good + bad = 270)
    (bound : bad ≤ 6*18+6*9+5*12) : 48 ≤ good := by omega
#print axioms costC
end ThreeTeams
