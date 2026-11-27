import Endgame
import BlockCatalogue

namespace Sharp40
open Endgame
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def pairs : List Pairing := [
  [(0, 9), (1, 13), (2, 7), (3, 12), (4, 14), (5, 6), (8, 11), (10, 15)],
  [(0, 7), (1, 11), (2, 8), (3, 4), (5, 10), (6, 9), (12, 14), (13, 15)],
  [(0, 10), (1, 8), (2, 4), (3, 11), (5, 7), (6, 13), (9, 14), (12, 15)],
  [(0, 11), (1, 10), (2, 6), (3, 13), (4, 7), (5, 12), (8, 14), (9, 15)],
  [(0, 12), (1, 14), (2, 10), (3, 5), (4, 13), (6, 7), (8, 15), (9, 11)],
  [(0, 13), (1, 9), (2, 14), (3, 6), (4, 10), (5, 8), (7, 12), (11, 15)],
  [(0, 14), (1, 6), (2, 9), (3, 10), (4, 8), (5, 13), (7, 15), (11, 12)],
  [(0, 8), (1, 3), (2, 5), (4, 12), (6, 11), (7, 13), (9, 10), (14, 15)],
  [(0, 15), (1, 4), (2, 3), (5, 11), (6, 8), (7, 10), (9, 12), (13, 14)],
  [(0, 4), (1, 7), (2, 15), (3, 9), (5, 14), (6, 10), (8, 12), (11, 13)],
  [(0, 6), (1, 15), (2, 13), (3, 8), (4, 11), (5, 9), (7, 14), (10, 12)],
  [(0, 5), (1, 2), (3, 15), (4, 9), (6, 14), (7, 11), (8, 10), (12, 13)],
  [(0, 1), (2, 12), (3, 14), (4, 6), (5, 15), (7, 8), (9, 13), (10, 11)],
  [(0, 2), (1, 12), (3, 7), (4, 5), (6, 15), (8, 9), (10, 13), (11, 14)],
  [(0, 3), (1, 5), (2, 11), (4, 15), (6, 12), (7, 9), (8, 13), (10, 14)]]
def matchings := pairs.map edgeSet
def startA := 14
def startB := 112
def edge (a b : Nat) := (1 <<< a) ||| (1 <<< b)
def proper := (List.range 16).all (fun v =>
  matchings.all (fun m => (m.filter (fun e => e.testBit v)).length == 1) &&
  (List.range 16).all (fun w => v==w || (matchings.filter (fun m => m.contains (edge v w))).length == 1))
def stopped (a b t : Nat) := matchings.any fun m =>
  closedAt m (1 ||| t) || closedAt m (outside ^^^ t) || closedAt m (a ||| t) || closedAt m (b ||| t)
def allNine := (List.range 512).filter (fun t => (BlockCatalogue.points t).size == 3)
def layouts := allNine.flatMap fun t => allNine.filterMap fun s =>
  let u := 511 ^^^ s ^^^ t
  if (t &&& s)==0 && t<s && s<u then some [t <<< 7,s <<< 7,u <<< 7] else none
def starts := (List.range 127).filter fun a =>
  let b := 126 ^^^ a
  (a &&& 1)==0 && (BlockCatalogue.points a).size == 3 && a<b &&
   !(matchings.any (fun m => closedAt m (1 ||| a) || closedAt m (1 ||| b)))
def wins (a : Nat) := (layouts.filter (fun row => row.all (fun t => !stopped a (126 ^^^ a) t))).length

theorem legal : proper = true := by native_decide
theorem forty_occurrences : (matchings.map (fun m => (blocked m startA startB).length)).sum = 40 := by native_decide
theorem point_fifteen : (allNine.filter (fun t => t.testBit 8)).length = 28 ∧
    allNine.all (fun t => !(t.testBit 8) || stopped startA startB (t <<< 7)) = true := by native_decide
theorem outcomes : layouts.length = 280 ∧ wins startA = 0 ∧
    (starts.map wins).sum = 211 := by native_decide

def winningGroups : List (List Nat) := [[1, 2, 4], [3, 5, 6], [7, 8, 9], [10, 11, 14], [12, 13, 15]]
def wild := winningGroups.flatMap (fun group =>
  [edge group[0]! group[1]!,edge group[1]! group[2]!])
def flood (lines : List Nat) : Nat → Nat → Nat
  | 0, seen => seen
  | k+1, seen => flood lines k (lines.foldl (fun grown e =>
      if (seen &&& e)==0 then grown else grown ||| e) seen)
def connects (omitRoot : Bool) (m : Teams.Matching) :=
  let keep := if omitRoot then 65534 else 65535
  let lines := (wild++m).filter (fun e => (e &&& keep)==e)
  flood lines 16 2 == keep
theorem ten_wild_edges_connect : wild.length = 10 ∧ wild.Nodup ∧
    matchings.all (fun m => connects true m && connects false m) = true := by native_decide
private def color (x y : Nat) := matchings.findIdx (fun m => m.contains (edge x y))
private def crossColors := [1,2,3].flatMap (fun x => [4,5,6].map (color x))
private def insideA := [color 1 2,color 1 3,color 2 3]
private def insideB := [color 4 5,color 4 6,color 5 6]

/-- All nine cross edges have different colors, the two inside palettes are
disjoint, and the six edges in each root quartet are distinct. Even this
start loses every completion. -/
theorem rainbow_start_fails : proper=true ∧ crossColors.Nodup ∧
    (insideA++insideB).Nodup ∧ (insideA++[color 0 1,color 0 2,color 0 3]).Nodup ∧
    (insideB++[color 0 4,color 0 5,color 0 6]).Nodup ∧ wins startA=0 := by
  refine ⟨legal,?_,?_,?_,?_,outcomes.2.1⟩ <;> native_decide

#print axioms rainbow_start_fails
#print axioms point_fifteen
#print axioms ten_wild_edges_connect
end Sharp40
