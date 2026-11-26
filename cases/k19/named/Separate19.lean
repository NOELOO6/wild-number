import PairCuts19
namespace Separate19
open PairCuts19
def bit (x : Nat) := 1 <<< x
def dropBit (x : Nat) := x &&& (x-1)
def low (x : Nat) := x ^^^ dropBit x
def edge (x y : Nat) := bit x ||| bit y
def shapes3 := #[(0,0,0,186192),(0,0,1,187360),(0,0,2,177600),(0,1,0,173808),
    (0,1,1,177600),(1,0,0,173808),(1,0,1,177600),(1,1,0,152640)]

def normalized (tt uu tu : Nat) := Id.run do
  let mut edges := #[]
  if tt=1 then edges := edges.push (edge 0 1)
  if uu=1 then edges := edges.push (edge 3 4)
  for i in [:tu] do edges := edges.push (edge (2*tt+i) (3+2*uu+i))
  let used := edges.foldl (· ||| ·) 0
  let mut next := 6
  for i in [:6] do
    if !used.testBit i then edges := edges.push (edge i next); next := next+1
  for j in [:((18-next)/2)] do edges := edges.push (edge (next+2*j) (next+2*j+1))
  return edges.push (bit 18)

def closed (es : Array Nat) := Id.run do
  let mut table := Array.replicate (bit 19) false
  for s in unions es do table := table.set! s true
  return table

/-- Test the 31 nonempty unions of triples. A disconnected component union
can always be chosen on the side excluding the group of four. -/
def finish (bad : Array Bool) (depth left : Nat) (sides : Array Nat) : Nat := Id.run do
  match depth with
  | 0 => return 1
  | k+1 =>
    let x := low left
    let mut ys := dropBit left
    let mut n := 0
    for _ in [:9] do
      if ys==0 then break
      let y := low ys
      ys := dropBit ys
      let mut zs := ys
      for _ in [:8] do
        if zs==0 then break
        let t := x ||| y ||| low zs
        zs := dropBit zs
        let extra := sides.map (· ||| t)
        if extra.all (fun v => !bad[v]!) then n := n+finish bad k (left ^^^ t) (sides++extra)
    return n

def count (tt uu tu : Nat) := Id.run do
  let b := closed (normalized tt uu tu)
  if b[7]! || b[56]! || b[63]! then return 0
  let mut n := 0
  for a in [6:19] do for c in [a+1:19] do for d in [c+1:19] do for e in [d+1:19] do
    let quad := (edge a c) ||| (edge d e)
    n := n+finish b 3 (((bit 19-1) ^^^ 63) ^^^ quad) #[0,7,56,63]
  return n

@[noinline] def readInts (s : String) := (s.trim.splitOn "\n").toArray.map
  (fun l => (l.splitOn " ").toArray.map String.toInt!)
def prices := readInts (include_str "vertex-prices.txt")
def inter (es : Array Nat) (s : Nat) :=
  (es.filter (fun e => (e &&& (e-1)) != 0 && e &&& s == e)).size

def values (a b : Array Nat) (ma mb mc : Nat) := Id.run do
  let mut v := Array.replicate 361 0
  for e in a do
    if e &&& (e-1) == 0 then continue
    let t := e ||| bit ma
    if t.testBit mb || t.testBit mc then continue
    for x in [:19] do for y in [x+1:19] do
      let u := edge x y ||| bit mc
      if x==mc || y==mc || t &&& u != 0 || u.testBit mb then continue
      let tt := inter b t
      let uu := inter b u
      let total := inter b (t ||| u)
      for (j,k,l,h) in shapes3 do
        if j==tt && k==uu && j+k+l==total then v := v.modify (19*x+y) (·+h)
  return v

def audit (i : Nat) := Id.run do
  let (aa,bb) := pairUnits types[i]!
  let a := aa.map (· >>> 1)
  let b := bb.map (· >>> 1)
  let ma := (a.find? (fun e => dropBit e == 0)).get!.log2
  let mb := (b.find? (fun e => dropBit e == 0)).get!.log2
  let mut row := i*17
  for mc in [:19] do
    if mc==ma || mc==mb then continue
    let v := values a b ma mb mc
    let p := prices[row]!
    row := row+1
    if p.size != 19 || p[mc]! != 0 || p.toList.sum < 2*5246080 then return false
    for x in [:19] do for y in [x+1:19] do
      let e := edge x y
      if x != mc && y != mc && !a.contains e && !b.contains e then
        if p[x]!+p[y]! > 2*(v[19*x+y]! : Int) then return false
  return true
end Separate19
