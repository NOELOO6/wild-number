import Std

namespace Cyclic15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev Edge := Nat × Nat
abbrev Pattern := List (List Nat)

def patterns : List Pattern := [
  [[0,5,10],[1,6,11],[2,7,12],[3,8,13],[4,9,14]],
  [[1,9,11],[3,5,10],[6,8,13],[4,12,14],[0,2,7]],
  [[3,8,10],[2,9,12],[5,11,14],[4,7,13],[0,1,6]]]

def points : List Nat := List.range 15
def distances : List Nat := [1,2,3,4,5,6,7]
def edgeFor (d a : Nat) : Edge := (a, (a+d)%15)
def edgeBits (e : Edge) : Nat := (1 <<< e.1) ||| (1 <<< e.2)
def room (used : Nat) (e : Edge) : Bool := (used &&& edgeBits e) == 0

/-- One oriented edge at each cyclic distance. Disjointness and the unused
    vertex 0 make its translates a near-one-factorization. -/
def Valid : List Nat → Nat → List Nat → Prop
  | [], _, xs => xs = []
  | d::ds, used, a::as =>
      a < 15 ∧ room used (edgeFor d a) = true ∧
      Valid ds (used ||| edgeBits (edgeFor d a)) as
  | _::_, _, [] => False

def build : List Nat → List Nat → List Edge → List Edge
  | d::ds, a::as, acc => build ds as (edgeFor d a :: acc)
  | _, _, acc => acc

def groupBits (vs : List Nat) : Nat := vs.foldl (fun s v => s ||| (1 <<< v)) 0
def unionBits (groups : Pattern) (which : Nat) : Nat :=
  (groups.zipIdx).foldl (fun s (g,i) =>
    if which.testBit i then s ||| groupBits g else s) 0

/-- Cross every nontrivial cut of the five connected wild groups, in each
    translate of the base matching. Cuts not containing group 4 suffice
    since the other side of a cut has exactly the same crossing edges. -/
def cutMasks (groups : Pattern) : List Nat :=
  ((List.range' 1 15).flatMap fun which =>
    points.map fun c =>
      let u := unionBits groups which
      -- Membership of v in this set means v+c lies on the chosen side.
      points.foldl (fun s v =>
        if u.testBit ((v+c)%15) then s ||| (1 <<< v) else s) 0).eraseDups

def crosses (es : List Edge) (side : Nat) : Bool :=
  es.any fun e => side.testBit e.1 != side.testBit e.2

def connects (groups : Pattern) (es : List Edge) : Bool :=
  (cutMasks groups).all (crosses es)

def wins (es : List Edge) : Bool := patterns.any (fun gs => connects gs es)

/-- A structurally recursive universal test over all remaining choices. -/
def check : List Nat → Nat → List Edge → Bool
  | [], _, es => wins es
  | d::ds, used, es => points.all fun a =>
    let e := edgeFor d a
    !room used e || check ds (used ||| edgeBits e) (e :: es)

theorem check_sound (ds : List Nat) (used : Nat) (es : List Edge)
    (starts : List Nat) (hc : check ds used es = true)
    (hv : Valid ds used starts) : wins (build ds starts es) = true := by
  induction ds generalizing used es starts with
  | nil => exact hc
  | cons d ds ih =>
    cases starts with
    | nil => exact False.elim hv
    | cons a as =>
      obtain ⟨ha, hr, hv'⟩ := hv
      have hm : a ∈ points := List.mem_range.mpr ha
      have hall := (List.all_eq_true.mp hc) a hm
      simp [hr] at hall
      exact ih _ _ _ hall hv'

-- Each list is genuinely a partition of the 15 vertices into five triples.
theorem partitions_are_five_triples : patterns.all (fun gs =>
    gs.length == 5 && gs.all (fun g => g.length == 3) &&
    points.all (fun v => gs.flatten.contains v)) = true := by decide

-- Exhaustion is split into separate closed terms to limit kernel memory.
theorem first_0 : (!room 1 (edgeFor 1 0) || check [2,3,4,5,6,7] (1 ||| edgeBits (edgeFor 1 0)) [edgeFor 1 0]) = true := by decide
theorem first_1 : (!room 1 (edgeFor 1 1) || check [2,3,4,5,6,7] (1 ||| edgeBits (edgeFor 1 1)) [edgeFor 1 1]) = true := by decide
theorem first_2 : (!room 1 (edgeFor 1 2) || check [2,3,4,5,6,7] (1 ||| edgeBits (edgeFor 1 2)) [edgeFor 1 2]) = true := by decide
theorem first_3 : (!room 1 (edgeFor 1 3) || check [2,3,4,5,6,7] (1 ||| edgeBits (edgeFor 1 3)) [edgeFor 1 3]) = true := by decide
theorem first_4 : (!room 1 (edgeFor 1 4) || check [2,3,4,5,6,7] (1 ||| edgeBits (edgeFor 1 4)) [edgeFor 1 4]) = true := by decide
theorem first_5 : (!room 1 (edgeFor 1 5) || check [2,3,4,5,6,7] (1 ||| edgeBits (edgeFor 1 5)) [edgeFor 1 5]) = true := by decide
theorem first_6 : (!room 1 (edgeFor 1 6) || check [2,3,4,5,6,7] (1 ||| edgeBits (edgeFor 1 6)) [edgeFor 1 6]) = true := by decide
theorem first_7 : (!room 1 (edgeFor 1 7) || check [2,3,4,5,6,7] (1 ||| edgeBits (edgeFor 1 7)) [edgeFor 1 7]) = true := by decide
theorem first_8 : (!room 1 (edgeFor 1 8) || check [2,3,4,5,6,7] (1 ||| edgeBits (edgeFor 1 8)) [edgeFor 1 8]) = true := by decide
theorem first_9 : (!room 1 (edgeFor 1 9) || check [2,3,4,5,6,7] (1 ||| edgeBits (edgeFor 1 9)) [edgeFor 1 9]) = true := by decide
theorem first_10 : (!room 1 (edgeFor 1 10) || check [2,3,4,5,6,7] (1 ||| edgeBits (edgeFor 1 10)) [edgeFor 1 10]) = true := by decide
theorem first_11 : (!room 1 (edgeFor 1 11) || check [2,3,4,5,6,7] (1 ||| edgeBits (edgeFor 1 11)) [edgeFor 1 11]) = true := by decide
theorem first_12 : (!room 1 (edgeFor 1 12) || check [2,3,4,5,6,7] (1 ||| edgeBits (edgeFor 1 12)) [edgeFor 1 12]) = true := by decide
theorem first_13 : (!room 1 (edgeFor 1 13) || check [2,3,4,5,6,7] (1 ||| edgeBits (edgeFor 1 13)) [edgeFor 1 13]) = true := by decide
theorem first_14 : (!room 1 (edgeFor 1 14) || check [2,3,4,5,6,7] (1 ||| edgeBits (edgeFor 1 14)) [edgeFor 1 14]) = true := by decide
theorem exhaustive_check : check distances 1 [] = true := by
  change (List.range 15).all (fun a => !room 1 (edgeFor 1 a) || check [2,3,4,5,6,7]
    (1 ||| edgeBits (edgeFor 1 a)) [edgeFor 1 a]) = true
  rw [show List.range 15 = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] from rfl]
  simp only [List.all_cons, List.all_nil, first_0, first_1, first_2, first_3, first_4, first_5, first_6, first_7, first_8, first_9, first_10, first_11, first_12, first_13, first_14, Bool.and_self]

theorem every_cyclic_starter (starts : List Nat) (hv : Valid distances 1 starts) :
    ∃ gs ∈ patterns, connects gs (build distances starts []) = true :=
  List.any_eq_true.mp (check_sound distances 1 [] starts exhaustive_check hv)

#print axioms Cyclic15.every_cyclic_starter
end Cyclic15
