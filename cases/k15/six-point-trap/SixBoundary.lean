import SixTrap

namespace SixBoundary
open VertexRedraw EdgeWalk WildDeletion

/-- Only the lines touching points 0 through 5 are prescribed. The partner at
15 is the missing color at an ordinary point. -/
def ref (c : C) (v : V) : V := Fin.ofNat' 16 FixedSix.rows[c.val]![v.val]!
def held (c : C) (v : V) := v.val < 6 || (ref c v).val < 6
def knownPairs (c : C) : R := points.filterMap fun x =>
  if held c x && decide (x < ref c x) then some (x,ref c x) else none
def free (c : C) := points.filter fun x => !held c x
def possible (c : C) := (fills 16 (free c)).map (knownPairs c ++ ·)

def hiddenPairs : R := points.flatMap fun x => points.filterMap fun y =>
  if 6 ≤ x.val ∧ x < y then some (x,y) else none

/-- Bit i is the Boolean test for item i in the list. -/
def bits {α : Type} (p : α → Bool) : List α → Nat
  | [] => 0
  | x :: xs => ((bits p xs) <<< 1) ||| (if p x then 1 else 0)

def wilds := FixedSix.all.map trial
structure Row where
  hidden : Nat
  wins : Nat
  deriving Inhabited, DecidableEq, Repr

def encodeWith (unfixed m : R) : Row :=
  let es := erase m
  ⟨bits (fun (e : Edge 16) => m.contains e || m.contains (e.2,e.1)) unfixed,
   bits (fun g => passes 0 (g ++ es)) wilds⟩

def encode := encodeWith hiddenPairs

def order : List C := [0,12,11,7,14,2,3,5,6,10,13,8,9,4,1]
def pools (cs : List C) := cs.map fun c => (possible c).map encode

/-- Remove one set bit on each step. This tests whether at least k bits are set. -/
def enough : Nat → Nat → Bool
  | 0, _ => true
  | k+1, s => s != 0 && enough k (s &&& (s-1))

structure Stats where
  completions : Nat := 0
  belowNineteen : Nat := 0
  deriving Inhabited, Repr, DecidableEq

def Stats.add (a b : Stats) : Stats :=
  ⟨a.completions+b.completions,a.belowNineteen+b.belowNineteen⟩

/-- Disjoint hidden edges, one option per color. Every chosen row contributes
its own graph-tested set of wins. -/
def scan : List (List Row) → Nat → Nat → Stats
  | [], _, alive => ⟨1, if enough 19 alive then 0 else 1⟩
  | opts :: rest, used, alive => opts.foldl (fun total r =>
    if used &&& r.hidden == 0 then total.add (scan rest (used ||| r.hidden) (alive &&& r.wins))
    else total) {}

def initial := 2^2800-1
end SixBoundary
