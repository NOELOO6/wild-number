import SixTrap
namespace LastNineteen
open VertexRedraw EdgeWalk WildDeletion

def original := FixedSix.all.filter FixedSix.succeeds
def rows := (numbers (include_str "three-color-change.txt")).map List.toArray
def touched := (List.range 15).filter fun c => rows[c]! != FixedSix.rows[c]!
def ordinary := rows.map fun m => actualEdges (fun v => Fin.ofNat' 16 m[v.val]!)
def verdict (g : List Nat) := SixTrap.classify (trial g) ordinary

theorem three_color_change : properRows rows=true ∧ touched=[3,5,14] ∧
    (rows.all (fun m => SixTrap.edgesInside 32831 m ≤ 2))=true ∧ original.length=19 ∧
    (original.all (fun g => decide (verdict g = .loss)))=true ∧
    (FixedSix.all.filter (fun g => decide (verdict g = .win))).length=81 ∧
    (FixedSix.all.filter (fun g => decide (verdict g = .loss))).length=2719 := by native_decide

theorem every_old_win_now_loses (g) (h : g∈original) :
    ∃ m∈ordinary,¬Connected (Adj (trial g++m)) :=
  SixTrap.loss_disconnected (of_decide_eq_true (List.all_eq_true.mp three_color_change.2.2.2.2.1 g h))

/-- Swapping the two color names independently on whole alternating cycles
gives exactly the valid two-color redraws. A bit records which name to use. -/
def stable (a b : Array Nat) (s : Nat) := (Array.range 16).all fun x =>
  s.testBit x == s.testBit a[x]! && s.testBit x == s.testBit b[x]!
def redraw (a b : Array Nat) (s : Nat) := (Array.range 16).map fun x =>
  if s.testBit x then b[x]! else a[x]!
def asEdges (a : Array Nat) := actualEdges (fun v => Fin.ofNat' 16 a[v.val]!)
def retained (a b : Array Nat) := (original.filter fun g =>
  let w := trial g
  passes 0 (w++asEdges a) && passes 0 (w++asEdges b)).length

def pairBounds (a b : Array Nat) := (List.range 65536).all fun s =>
  !stable a b s || (
    let u := redraw a b s
    let v := redraw b a s
    let n := retained u v
    n ≥ 3 && (SixTrap.edgesInside 32831 u > 2 || SixTrap.edgesInside 32831 v > 2 || n ≥ 10))
end LastNineteen
