import FixedSix

namespace SixTrap
open VertexRedraw EdgeWalk WildDeletion

def rows := (numbers (include_str "coloring.txt")).map List.toArray
def ordinary := rows.map fun m => actualEdges (fun v => Fin.ofNat' 16 m[v.val]!)

/-- Classify a grouping by following actual old and wild edges on fifteen points.
Every loss must supply a nonempty separating set with no edge leaving it. -/
inductive Verdict | win | loss | unchecked deriving BEq, DecidableEq, Inhabited

def classify (wild : E) : List E → Verdict
  | [] => .win
  | color :: rest =>
    let edges := wild ++ color
    let seen := run edges 15 1
    if seen == 32767 then classify wild rest
    else if isolates seen edges then .loss else .unchecked

theorem win_connected {wild : E} {cs : List E} (h : classify wild cs = .win) :
    ∀ m ∈ cs, Connected (Adj (wild ++ m)) := by
  induction cs with
  | nil => simp
  | cons m ms ih =>
    simp only [classify] at h
    split at h
    · rename_i test
      intro c hc
      rcases List.mem_cons.mp hc with rfl|mem
      · exact connected_of_passes (0 : Fin 15) _ test
      · exact ih h c mem
    · split at h <;> contradiction

theorem loss_disconnected {wild : E} {cs : List E} (h : classify wild cs = .loss) :
    ∃ m ∈ cs, ¬ Connected (Adj (wild ++ m)) := by
  induction cs with
  | nil => contradiction
  | cons m ms ih =>
    simp only [classify] at h
    split at h
    · obtain ⟨c,mem,bad⟩ := ih h
      exact ⟨c,List.mem_cons_of_mem _ mem,bad⟩
    · split at h
      · exact ⟨m,List.mem_cons_self,isolated_not_connected (by assumption)⟩
      · contradiction

def before := [7,56,448,11264,20992]
def afterSwap := before.map (swapBit 3 9)
def edgesInside (s : Nat) (m : Array Nat) := ((List.range 16).filter fun x =>
  s.testBit x && s.testBit m[x]! && x<m[x]!).length
def closed (s : Nat) (m : Array Nat) := (List.range 16).all fun x =>
  !s.testBit x || s.testBit m[x]!
def prelim := FixedSix.starts.filter fun blocks => blocks.all fun t =>
  rows.all fun m => !closed (t ||| 32768) m
def startingTriples := (FixedSix.triplesOn 0 15).filter fun t =>
  (rows.filter (closed (t ||| 32768))).length = 3
def imageSet (s : Nat) (m : Array Nat) := (List.range 16).foldl (fun z x =>
  if s.testBit x then z ||| 2^m[x]! else z) 0
def outsideImageCount (t : Nat) :=
  let s := t ||| 32768
  ((rows.filter (fun m => !closed s m)).map (imageSet s)).eraseDups.length

def exceptionColors := (List.range 15).filter fun c => edgesInside 32831 rows[c]! > 2
theorem fixture : properRows rows = true ∧ rows.all (fun m => !closed 63 m) = true ∧
    exceptionColors = [8,10,14] ∧ prelim.length = 4 ∧ startingTriples = [10244] ∧
    outsideImageCount 10244 = 12 := by native_decide

theorem local_record : FixedSix.all.length = 2800 ∧
    (FixedSix.all.all (fun g => decide (classify (trial g) ordinary = .loss))) = true ∧
    before ∈ FixedSix.all ∧ afterSwap = [7,560,448,11264,20488] ∧
    (trial afterSwap).length = 10 ∧ (trial afterSwap).Nodup ∧
    classify (trial afterSwap) ordinary = .win := by native_decide

theorem every_fixed_six_loses (g : List Nat) (hg : g ∈ FixedSix.all) :
    ∃ m ∈ ordinary, ¬ Connected (Adj (trial g ++ m)) :=
  loss_disconnected (of_decide_eq_true (List.all_eq_true.mp local_record.2.1 g hg))

theorem one_exchange_works : ∀ m ∈ ordinary, Connected (Adj (trial afterSwap ++ m)) :=
  win_connected local_record.2.2.2.2.2.2

/-- Enumerate triples by their least point, with two larger partners. -/
def choices := (Array.range 15).map fun a => Id.run do
  let mut triples := #[]
  for b in [a+1:15] do
    for c in [b+1:15] do triples := triples.push (2^a ||| 2^b ||| 2^c)
  return triples

/-- Count by verdict. The least unused point belongs to exactly one next group.
Stopping at the final three points avoids scanning unnecessary last choices. -/
structure Tally where
  wins : Nat := 0
  losses : Nat := 0
  unchecked : Nat := 0
  deriving DecidableEq, Repr, Inhabited

def note (cs : List E) (g : List Nat) (t : Tally) :=
  match classify (trial g) cs with
  | .win => {t with wins := t.wins+1}
  | .loss => {t with losses := t.losses+1}
  | .unchecked => {t with unchecked := t.unchecked+1}

def visit (cs : List E) : Nat → Nat → List Nat → Tally → Tally
  | 0, left, groups, acc => note cs (left :: groups) acc
  | depth+1, left, groups, acc =>
    let first := (left &&& (left ^^^ (left-1))).log2
    choices[first]!.foldl (fun totals t =>
      if left &&& t == t then visit cs depth (left ^^^ t) (t::groups) totals else totals) acc

end SixTrap
