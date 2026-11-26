import BlockCatalogue
import Endgame

namespace Completion
open BlockCatalogue Endgame
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def order (s : Nat) := BlockCatalogue.pc s.toUInt64
def excessive (h : Array Nat) (r : Rule) := (Array.range 512).any fun w =>
  order w == r.size && (h.foldl (fun sum t => sum + r.w[order (t &&& w)]!) 0) > r.limit
def ruledOut (h : Array Nat) := h.size > 40 || rules40.any (excessive h)

theorem no_forty_point_pattern : catalogue.all ruledOut = true := by native_decide

def allTriples := (Array.range 512).filter (fun t => order t == 3)
def divisions := allTriples.flatMap fun t => allTriples.filterMap fun s =>
  let u := 511 ^^^ t ^^^ s
  if (t &&& s) == 0 && t < s && s < u then some (t,s,u) else none
def covers (h : Array Nat) := divisions.all fun (a,b,c) =>
  h.contains a || h.contains b || h.contains c
def minimal (h : Array Nat) := h.all fun t => divisions.any fun (a,b,c) =>
  ((a==t && !h.contains b && !h.contains c) ||
   (b==t && !h.contains a && !h.contains c) ||
   (c==t && !h.contains a && !h.contains b))

theorem listed_obstructions : catalogue.size = 899 ∧ divisions.size = 280 ∧
    catalogue.all (fun h => covers h && minimal h) = true := by native_decide
#print axioms no_forty_point_pattern
#print axioms listed_obstructions
end Completion
