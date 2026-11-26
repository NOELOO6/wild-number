import Std
namespace Counting
set_option maxRecDepth 300000
set_option maxHeartbeats 0
abbrev Vec := Array Int
def readRows (s : String) := (((s.splitOn "\n").filter (fun t => !t.isEmpty)).map
  (fun t => (((t.splitOn " ").filter (fun w => !w.isEmpty)).map (fun w => w.toInt?.getD 0)).toArray)).toArray
def natRows (s : String) := (readRows s).map (fun v => v.map Int.toNat)
def graphs := (natRows (include_str "patterns.txt")).map (fun v => (v.toList.drop 1))
def rawPrices := readRows (include_str "prices.txt")
def squares := readRows (include_str "squares.txt")
def expansions := readRows (include_str "expansions.txt")
def flagTypes := natRows (include_str "flag-types.txt")
def bit (n : Nat) := 1 <<< n
def points := List.range 12
def counts : Array Nat := Id.run do
  let mut v := #[0]
  for i in List.range' 1 4095 do v := v.push (v[i/2]! + i%2)
  return v
def pc (m : Nat) := counts[m]!
def triples := (List.range 4096).filter (fun m => pc m == 3)
def perms : List Nat → Nat → List (List Nat)
  | _, 0 => [[]]
  | xs, k+1 => xs.flatMap fun i => (perms (xs.erase i) k).map (i :: ·)
def signatures (e : List Nat) :=
  (points.map fun v => e.zipIdx.foldl (fun t (s,i) => if s.testBit v then t ||| bit i else t) 0).mergeSort
def key' (e : List Nat) :=
  (signatures e).foldl (fun k x => 16*k+x) 0
def permutations (e : List Nat) := (perms (List.range e.length) e.length).map (fun p => p.map (e[·]!))
def key (e : List Nat) := (bit (48+3*e.length)) +
  ((permutations e).map key').foldl min (bit 48)
def keys := graphs.map key
def lookup (e : List Nat) := keys.toList.idxOf (key e)
def fact (n : Nat) := (List.range' 1 n).foldl (· * ·) 1
def choose (a b : Nat) := if b>a then 0 else fact a/(fact b*fact (a-b))
def copies (e : List Nat) :=
  let sig := signatures e
  let sym := ((permutations e).filter (fun f => signatures f == sig)).length
  let d := (List.range (bit e.length)).foldl (fun n j => n*fact (sig.count j)) 1
  fact 12/(sym*d)
def multiplicities := graphs.map copies
def addAt (a : Vec) (i : Nat) (x : Int) := a.modify i (· + x)
def allPresent (e : List Nat) (s : Nat) :=
  (e.zipIdx.filter (fun (_,i) => s.testBit i)).map Prod.fst
def extensions (e : List Nat) (v : Nat) := triples.filter (fun t =>
  !e.contains t && (v==12 || t.testBit v))
def extCounts (e : List Nat) (v : Nat) := (extensions e v).foldl
  (fun (a : Vec) t => addAt a (lookup (t::e)) 1) (Array.replicate graphs.size 0)
def allExt := graphs.map (fun e => if e.length<4 then
  ((List.range 13).map (extCounts e)).toArray else #[])
def required (e : List Nat) (s : Nat) : Vec := Id.run do
  let mut a := Array.replicate graphs.size (0 : Int)
  for u in List.range (bit e.length) do
    if (u &&& s) == 0 then
      a := addAt a (lookup (allPresent e (s ||| u))) (if pc u%2==0 then 1 else -1)
  return a
def checkedPatterns := graphs.size==83 && graphs[0]! == [] && keys.toList.eraseDups.length==83 &&
  graphs.all (fun e => e.length≤4 && e.all (fun t => t<4096 && pc t==3) &&
    e.eraseDups.length==e.length && (e.length≥4 || (extensions e 12).all
      (fun t => lookup (t::e) < graphs.size)))
theorem pattern_coverage : checkedPatterns = true := by native_decide

def common (e : List Nat) := pc (e.foldl (· &&& ·) 4095)
def disjoint (e : List Nat) := pc (e.foldl (· ||| ·) 0) == 3*e.length
def denom : Int := 10^44
def goalPrices := graphs.map fun e =>
  if disjoint e then denom*15400*(choose 4 e.length : Nat)*(if e.length%2==0 then 1 else -1) else 0
def degrees (m : Nat) := (List.range 4).flatMap fun k =>
  ((List.range (19+3*k)).filter (fun d => 18+3*k-d≤75-m)).map (fun d => (k,d))
def degRows (m : Nat) (t : Nat) : Vec :=
  (graphs.mapIdx fun i e => if e.length==t then ((multiplicities[i]! * common e : Nat) : Int) else 0) ++
  ((degrees m).map (fun (_,d) => -(choose d t : Int))).toArray
def histRows (m i : Nat) : Vec := Array.replicate graphs.size 0 ++
  ((degrees m).map (fun (k,d) => ((if i==0 then 1 else if i==1 then k else d) : Int))).toArray

/-- Each row supplies either an exact double-counting identity, or a
    nonnegative count with a multiplier of the appropriate sign. -/
def row (m kind i j k : Nat) (weight : Int) : Option (Vec × Int) := Id.run do
  let zero := Array.replicate graphs.size (0:Int)
  if kind==0 then return some (zero.set! 0 1,1)
  if kind==1 && i<3 then return some (histRows m i, if i==0 then 12 else if i==1 then 3 else 3*m)
  if kind==2 && 0<i && i≤4 then return some (degRows m i,0)
  if kind==3 && i<graphs.size && graphs[i]!.length<4 && j≤12 && k≤1 then
    if j != 12 && ((k==0 && weight<0) || (k==1 && weight>0)) then return none
    let inside := (graphs[i]!.filter (fun t => j==12 || t.testBit j)).length
    let b := if j==12 then m else if k==0 then 18-(75-m) else 27
    return some (addAt (allExt[i]![j]!) i ((inside : Int)-b),0)
  if kind==4 && i<graphs.size && j<bit graphs[i]!.length && 0≤weight then
    return some (required graphs[i]! j,0)
  if kind==6 && i<expansions.size && 0≤weight then return some (expansions[i]!,0)
  return none

def lowerBound (m : Nat) : Int := Id.run do
  let mut c := goalPrices ++ Array.replicate (degrees m).length 0
  let mut v : Int := 0
  for z in rawPrices do
    if z[0]!.toNat==m then
      if z.size != 6 then return -denom
      let lam := z[5]!
      match row m z[1]!.toNat z[2]!.toNat z[3]!.toNat z[4]!.toNat lam with
      | none => return -denom
      | some (a,rhs) =>
        v := v+lam*rhs
        for i in [:a.size] do c := c.modify i (fun x => x-lam*a[i]!)
  for i in [:c.size] do v := v+(min 0 c[i]!)*(if i<graphs.size then 1 else 12)
  return v
theorem twelve_bounds : ((List.range' 64 12).all (fun m => decide (2301*denom < lowerBound m))) = true := by
  native_decide
#print axioms pattern_coverage
#print axioms twelve_bounds
end Counting
