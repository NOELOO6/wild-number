import Std
namespace K19Placement
/-- One entry per current connected component. Its two counts are the free
slots and the already placed endpoints still waiting for their partners. -/
abbrev Shape := List Nat
def free (x : Nat) := x/32
def waiting (x : Nat) := x%32
def freeSlots (s : Shape) := (s.map free).sum
def start : Shape := [1,96,96,96,96,96,128]
def actions (s : Shape) : List (Option Nat) :=
  (if (s.map waiting).sum < freeSlots s then [none] else []) ++
    (s.zipIdx.filterMap fun (v,i) => if waiting v > 0 then some (some i) else none)

def move (s : Shape) (a : Option Nat) (b : Nat) : Shape :=
  let v := s[b]!
  let cell := match a with
    | none => 32*(free v-1)+(waiting v+1)
    | some i => if i == b then 32*(free v-1)+(waiting v-1) else
        let u := s[i]!
        32*(free v+free u-1)+(waiting v+waiting u-1)
  ((s.zipIdx.filterMap fun (u,i) =>
    if i == b then some cell else if a == some i then none else some u).mergeSort (· ≤ ·))

/-- Each free slot is one possible choice, even when other slots are in the
same component. The action opens a color edge or closes a particular one. -/
def tickets (s : Shape) (a : Option Nat) : List Shape :=
  s.zipIdx.flatMap fun (v,b) => List.replicate (free v) (move s a b)

def parse (line : String) : Shape × Nat :=
  let xs := (line.splitOn " ").map String.toNat!
  (xs.tail, xs.head!)
def table : Std.HashMap Shape Nat := Std.HashMap.ofList
  ((((include_str "states.txt").splitOn "\n").filter (· != "")).map parse)
def val (s : Shape) := table[s]?.getD 0
def known (s : Shape) := table.contains s
def rowOK (s : Shape) (v : Nat) :=
  if freeSlots s == 0 then v == s.length-1 else
    (actions s).all fun a => let ts := tickets s a
      ts.all known && (ts.map val).sum == v
end K19Placement
