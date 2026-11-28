import CyclicCuts

namespace Wild15.Steiner
open EdgeWalk WildExact.Rotation.CutTest

abbrev V := Fin 15
abbrev Pair := V × V

structure Block where
  a : V
  b : V
  c : V
deriving Inhabited, DecidableEq

def member (T : Block) (x : V) := x==T.a || x==T.b || x==T.c
def blockMask (T : Block) := 2^T.a.val ||| 2^T.b.val ||| 2^T.c.val

/-- Each row records the point pairs still available for a Steiner triple. -/
abbrev Bank := Array Nat
def row (B : Bank) (x : V) := B[x.val]!
def free (B : Bank) (x y : V) := (row B x).testBit y.val

def initial : Bank := Array.ofFn fun x : V => 32767 ^^^ 2^x.val

def eraseBlock (B : Bank) (T : Block) : Bank :=
  let keep := 32767 ^^^ blockMask T
  Array.ofFn fun x : V => if member T x then row B x &&& keep else row B x

def points := List.finRange 15
def pairs : List Pair := points.flatMap fun x => (points.filter (fun y => x<y)).map (x,·)

private def bitCounts := (Array.range 32768).map fun mask => (List.range 15).countP (mask.testBit ·)

/-- Branch on a pair with few available third points. The correctness
argument only uses the pair's availability, independently of this choice. -/
def pivot (B : Bank) : Option Pair := Id.run do
  let mut best := none
  let mut lowest := 16
  for p in pairs do
    if free B p.1 p.2 then
      let count := bitCounts[row B p.1 &&& row B p.2]!
      if count<lowest then
        best := some p
        lowest := count
        if count≤1 then return best
  return best

def opposite (T : Block) (i : V) : Option Pair :=
  if i=T.a then some (T.b,T.c) else if i=T.b then some (T.a,T.c)
  else if i=T.c then some (T.a,T.b) else none

def edgesOf (ts : List Block) (i : V) := ts.filterMap (opposite · i)

def search (test : List Block → Bool) : Nat → Bank → List Block → Bool
  | 0,_,ts => test ts
  | k+1,B,ts => match pivot B with
    | none => test ts
    | some (x,y) =>
      if x=y ∨ free B x y=false then test ts else
        points.all fun z => !free B x z || !free B y z ||
          search test k (eraseBlock B ⟨x,y,z⟩) (⟨x,y,z⟩::ts)

def bankOf (ts : List Block) := ts.foldl eraseBlock initial

/-- Points 0, 1 and 2 lie on the first line. The other twelve points
are six pairs of color 0, indexed by the indicated permutation for color 1. -/
def left (i : Fin 6) : V := ⟨3+2*i.val,by omega⟩
def right (i : Fin 6) : V := ⟨4+2*i.val,by omega⟩

def seeds (next : Fin 6 → Fin 6) : List Block :=
  ⟨0,1,2⟩ :: ((List.finRange 6).map (fun i => ⟨0,left i,right i⟩)) ++
    (List.finRange 6).map (fun i => ⟨1,left i,right (next i)⟩)

end Wild15.Steiner
