import Teams
namespace ThreeExceptions
open Teams
set_option maxHeartbeats 0
set_option maxRecDepth 200000
abbrev Perm := Array Nat
abbrev Graph := Array Nat
abbrev G8 := Nat
def eight := List.range 8
def vertices := List.range 16
def parse (doc : String) := ((doc.splitOn "\n").filter (fun s => !s.isEmpty)).map
  fun s => ((s.splitOn " ").filter (fun t => !t.isEmpty)).map (fun t => t.toNat?.getD 999999999)
structure Rep where
  kind : Nat
  red : G8
  blue : G8
deriving Inhabited
def reps := (parse (include_str "graphs.txt")).map fun xs => Rep.mk xs[0]! xs[1]! xs[2]!
def choices := parse (include_str "choices.txt")
def shapes := #[[8],[5,3],[4,4],[8],[6,2],[5,3],[4,4],[4,2,2],[3,3,2],[2,2,2,2]]
def permList : Nat → List Nat → List (List Nat)
  | 0, _ => [[]]
  | k+1, xs => xs.flatMap fun x => (permList k (xs.erase x)).map (x :: ·)
def perms := (permList 8 eight).map List.toArray
def edgeId (i j : Nat) := let a := max i j; a*(a-1)/2+min i j
def smallEdges := eight.flatMap fun i => (List.range i).map fun j => (i,j)
def edgeIndex (i j : Nat) := bit (edgeId i j)
def cycleMap (k : Nat) : Perm := Id.run do
  let mut start := 0
  let mut p := #[]
  for n in shapes[k]! do
    for i in List.range n do p := p.push (start+(i+1)%n)
    start := start+n
  return p
def outline (p : Perm) := eight.foldl (fun z i => z ||| edgeIndex i p[i]!) 0
def img (g : G8) (p : Perm) := smallEdges.foldl (fun z (a,b) =>
  if g.testBit (edgeId a b) then z ||| edgeIndex p[a]! p[b]! else z) 0
def permsFor (k : Nat) :=
  let q := cycleMap k
  let r := outline q
  perms.filter fun p => if k<3 then img r p == r else eight.all (fun i => p[q[i]!]! == q[p[i]!]!)
def distinct (xs : List Nat) := (xs.foldl (fun (s : Std.HashSet Nat) x => s.insert x) {}).toList
def pairings8 := distinct <| perms.map fun p =>
  (List.range 4).foldl (fun z i => z ||| edgeIndex p[2*i]! p[2*i+1]!) 0
def twoRegular := distinct <| (List.range 3).flatMap fun k =>
  let g := outline (cycleMap k)
  perms.map (img g)
def packed (r b : G8) := (r <<< 28) ||| b
def covers (k : Nat) : Bool := Id.run do
  let q := cycleMap k
  let syms := permsFor k
  let mut seen : Std.HashSet Nat := {}
  for g in reps do
    if g.kind == k then
      for p in syms do seen := seen.insert (packed (img g.red p) (img g.blue p))
  if k<3 then return twoRegular.all fun b => seen.contains (packed (outline q) b)
  return pairings8.all fun a => pairings8.all fun b => seen.contains (packed a b)

theorem coverage : pairings8.length = 105 ∧ twoRegular.length = 3507 ∧
    reps.length = 4983 ∧ (List.range 10).all covers = true := by native_decide

def cubic (s : Rep) : Graph := Id.run do
  let q := cycleMap s.kind
  let mut g := Array.replicate 16 0
  for (i,j) in smallEdges do
    if s.red.testBit (edgeId i j) then
      g := (g.modify i (· ||| bit j)).modify j (· ||| bit i)
    if s.blue.testBit (edgeId i j) then
      g := (g.modify (i+8) (· ||| bit (j+8))).modify (j+8) (· ||| bit (i+8))
  for i in eight do
    g := (g.modify i (· ||| bit (i+8))).modify (i+8) (· ||| bit i)
    if 3 ≤ s.kind then
      g := (g.modify i (· ||| bit (q[i]!+8))).modify (q[i]!+8) (· ||| bit i)
  return g

/-- Pack the partner of vertex i into digit i in base sixteen. -/
def putPair (a b : Nat) := (b <<< (4*a)) ||| (a <<< (4*b))
def mate (m i : Nat) := (m >>> (4*i)) % 16
def enumerate (g : Graph) : Nat → List Nat → List Nat
  | 0, [] => [0]
  | k+1, a::as => (as.filter (fun b => g[a]!.testBit b)).flatMap fun b =>
    (enumerate g k (as.erase b)).map (· ||| putPair a b)
  | _, _ => []
def decompositions (g : Graph) :=
  let ms := (enumerate g 8 vertices).mergeSort
  ms.flatMap fun a => ms.filterMap fun b => Id.run do
    if a ≥ b then return none
    let mut c := 0
    for v in vertices do
      let u := mate a v
      let w := mate b v
      if u == w then return none
      let last := g[v]! ^^^ bit u ^^^ bit w
      if last == 0 || (last &&& (last-1)) != 0 then return none
      c := c ||| (last.log2 <<< (4*v))
    return if b<c then some (a,b,c) else none

def inside (m : Nat) := (eight.filter (fun i => mate m i < 8)).length / 2
def ordinary (m : Nat) := inside m == 0 || inside m == 4
/-- Name the selected root 0 and its team red. This permutation is its
    own inverse after reversing the two operations in the other order. -/
def rootName (r v : Nat) :=
  let u := if r≥8 then v ^^^ 8 else v
  if u==r%8 then 0 else if u==0 then r%8 else u
def renumber (r m : Nat) := vertices.foldl (fun z i =>
  z ||| ((rootName r (mate m i)) <<< (4*(rootName r i)))) 0
def excluded (ms : List Nat) (a b : Nat) := ms.any fun m => mate m a == b
def unused (ms : List Nat) (a b : Nat) := if excluded ms a b then 0 else 1
/-- Bring the selected anchor to the fixed labels 1,8,9 for Teams.cost. -/
def anchorNames (a b c : Nat) : Perm := Id.run do
  let mut p := #[]
  let mut red := 2
  let mut blue := 10
  for v in vertices do
    if v==0 then p := p.push 0
    else if v==a then p := p.push 1
    else if v==b then p := p.push 8
    else if v==c then p := p.push 9
    else if v<8 then
      p := p.push red
      red := red+1
    else
      p := p.push blue
      blue := blue+1
  return p
def price (p : Perm) (m : Nat) := cost ((vertices.filter (fun i => i<mate m i)).map
    fun i => pair p[i]! p[mate m i]!)
def passes (t a b c : Nat) (ms : List Nat) :=
  let ordinaryCost := 96*t + 120*(unused ms 0 a+unused ms b c) +
    60*(12-t) - 60*(unused ms 0 b+unused ms 0 c) + 240*(unused ms a b+unused ms a c)
  let p := anchorNames a b c
  decide (ordinaryCost + (ms.map (price p)).sum < 1800)
def check (t code : Nat) (ms : List Nat) :=
  if code == 0 then ms.any ordinary else
    let data := code-1
    let r := data%16
    let a := (data/16)%8
    let b := 8+(data/128)%8
    let good := data/1024
    let xs := ms.map (renumber r)
    let cs := (List.range' 8 8).filter fun c => good.testBit (c-8)
    a != 0 && !cs.contains b && good < 256 &&
    decide (unused xs 0 a+unused xs 0 b+unused xs a b < cs.length) &&
    cs.all fun c => passes t a b c xs
def checkRow (s : Rep) (ws : List Nat) :=
  let ds := decompositions (cubic s)
  ws.length == ds.length+1 && ws.head? == some ds.length &&
  (ds.zip (ws.drop 1)).all fun ((a,b,c),w) => check (if s.kind<3 then 5 else 6) w [a,b,c]
theorem all_decompositions : reps.length = choices.length ∧
    (reps.zip choices).all (fun (g,ws) => checkRow g ws) = true := by native_decide
theorem case_counts : ((choices.map (fun xs => xs.head?.getD 0)).sum = 43564) ∧
    ((choices.map (fun xs => ((xs.drop 1).filter (· == 0)).length)).sum = 30253) := by native_decide
#print axioms coverage
#print axioms all_decompositions
end ThreeExceptions
