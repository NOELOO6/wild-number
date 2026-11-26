import ThreeExceptions
namespace EveryDeletion
open Teams ThreeExceptions
set_option maxHeartbeats 0
set_option maxRecDepth 300000
def fixedRows := parse (include_str "fixed-roots.txt")
def overlapRows := (parse (include_str "overlap-choices.txt")).toArray

def lossTable : Array Nat := Id.run do
  let mut result := Array.replicate 65536 0
  for (g,i) in catalogue.zipIdx do
    let b := bit i
    for v in cuts g do result := result.modify v (· ||| b)
  return result
def lost (m : Matching) :=
  (closedSides m).foldl (fun z s => z ||| lossTable[s]!) 0
def edgeCode (m : Matching) := m.foldl (fun z e =>
  let j := e.log2
  let i := (e ^^^ bit j).log2
  z ||| bit (edgeId i j)) 0
def partnerCode (m : Matching) := m.foldl (fun z e =>
  let j := e.log2; let i := (e ^^^ bit j).log2
  z ||| putPair i j) 0
def partnersToEdges (p : Perm) (m : Nat) :=
  (vertices.filter (fun i => i < mate m i)).map fun i => pair p[i]! p[mate m i]!

def smallCounts : Array Nat := Id.run do
  let mut a := #[0]
  for i in List.range' 1 65535 do a := a.push (a[i/2]! + i%2)
  return a
def bitCountAux : Nat → Nat → Nat → Nat
  | 0, _, s => s
  | n+1, v, s => if v==0 then s else bitCountAux n (v >>> 16) (s+smallCounts[v%65536]!)
def bitCount (x : Nat) := bitCountAux 113 x 0
structure Pure where
  edges : Nat
  partners : Nat
  bad : Nat
deriving Inhabited
def allowedInside : Array Pure := ((intra.filter (fun m => !(m.contains qa && m.contains qb))).map
  fun m => Pure.mk (edgeCode m) (partnerCode m) (lost m)).toArray

/-- Any pure-safe completion uses one within-team matching through each
    available within-team edge from v. Each such matching loses at least
    the indicated minimum number of layouts already lost to a mixed color. -/
def deduction (known occupied v : Nat) : Nat := Id.run do
  let mut minima := Array.replicate 16 1800
  for m in allowedInside do
    if (known &&& m.edges) == 0 then
      let y := mate m.partners v
      let a := bitCount (m.bad &&& occupied)
      minima := minima.modify y (min a)
  let mut saved := 0
  for y in vertices do
    if y != v && y/8==v/8 && !known.testBit (edgeId v y) then saved := saved+minima[y]!
  return saved

def cheap (t a b c : Nat) (ms : List Nat) (details : List Nat) :=
  let base := 96*t + 120*(unused ms 0 a+unused ms b c) +
    60*(12-t) - 60*(unused ms 0 b+unused ms 0 c) + 240*(unused ms a b+unused ms a c)
  let p := anchorNames a b c
  let edges := ms.map (partnersToEdges p)
  let bad := edges.foldl (fun z m => z ||| lost m) 0
  let cost := base+bitCount bad
  if cost<1800 then true else
    details.any fun w =>
      let k := w/8-1
      w%8 == c-8 && w/8>0 && k/17==16 && k%17<16 &&
      decide (cost < 1800+deduction (edges.foldl (fun z m => z ||| edgeCode m) 0) bad p[k%17]!)

def fixedCheck (t r code : Nat) (ms : List Nat) :=
  let ix := code/20000
  let d := code%20000-1
  let a := d%8
  let b := 8+d/8%8
  let mask := d/64
  let cs := (List.range' 8 8).filter (fun c => mask.testBit (c-8))
  let xs := ms.map (renumber r)
  let extra := if ix==0 then [] else overlapRows[ix-1]?.getD []
  code%20000 != 0 && a != 0 && !cs.contains b && mask<256 &&
    decide (unused xs 0 a+unused xs 0 b+unused xs a b < cs.length) &&
    cs.all (fun c => cheap t a b c xs extra)

def instanceList := reps.flatMap fun g =>
  ((decompositions (cubic g)).filterMap fun (a,b,c) =>
    if [a,b,c].any ordinary then none else some (if g.kind<3 then 5 else 6,[a,b,c]))
def checkRow (s : Nat × List Nat) (ws : List Nat) := ws.length==16 &&
  (ws.zipIdx.all fun (w,r) => fixedCheck s.1 r w s.2)

theorem every_fixed_root : instanceList.length = 13311 ∧
    fixedRows.length = instanceList.length ∧
    (instanceList.zip fixedRows).all (fun (s,ws) => checkRow s ws) = true := by native_decide
#print axioms every_fixed_root
end EveryDeletion
