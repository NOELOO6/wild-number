import BlockCatalogue
import Endgame

/- An integer price certificate for every admissible seven-point start of
   score at most 39. The nine outside points can be divided into two or three
   cells. Each price bound applies to every division of the indicated sizes. -/
namespace Score39
open BlockCatalogue
set_option maxHeartbeats 0
set_option maxRecDepth 200000

structure Price where
  sizes : Array Nat
  weights : Array Nat
  edge : Array Int
  color : Array Int
  witnesses : Array Nat
deriving Inhabited
def kinds : Array (Array Nat) := #[#[0, 0, 0, 0, 0], #[0, 0, 0, 0, 1], #[0, 0, 0, 1, 0], #[0, 0, 0, 1, 1], #[0, 0, 0, 2, 0], #[0, 0, 1, 0, 0], #[0, 0, 1, 0, 1], #[0, 0, 1, 1, 0], #[0, 1, 0, 0, 0], #[0, 1, 0, 1, 0], #[0, 1, 1, 0, 0], #[1, 0, 0, 0, 0], #[1, 0, 0, 0, 1], #[1, 0, 0, 1, 0]]

def examples : Array Endgame.Pairing := #[
  [(0, 15), (1, 14), (2, 13), (3, 12), (4, 11), (5, 10), (6, 9), (7, 8)],
  [(6, 5), (0, 15), (1, 14), (2, 13), (3, 12), (4, 11), (7, 8), (9, 10)],
  [(3, 6), (0, 15), (1, 14), (2, 13), (4, 12), (5, 11), (7, 8), (9, 10)],
  [(3, 6), (5, 4), (0, 15), (1, 14), (2, 13), (7, 8), (9, 10), (11, 12)],
  [(3, 6), (2, 5), (0, 15), (1, 14), (4, 13), (7, 8), (9, 10), (11, 12)],
  [(3, 2), (0, 15), (1, 14), (4, 13), (5, 12), (6, 11), (7, 8), (9, 10)],
  [(3, 2), (6, 5), (0, 15), (1, 14), (4, 13), (7, 8), (9, 10), (11, 12)],
  [(3, 2), (1, 6), (0, 15), (4, 14), (5, 13), (7, 8), (9, 10), (11, 12)],
  [(0, 6), (1, 15), (2, 14), (3, 13), (4, 12), (5, 11), (7, 8), (9, 10)],
  [(0, 6), (3, 5), (1, 15), (2, 14), (4, 13), (7, 8), (9, 10), (11, 12)],
  [(0, 6), (3, 2), (1, 15), (4, 14), (5, 13), (7, 8), (9, 10), (11, 12)],
  [(0, 3), (1, 15), (2, 14), (4, 13), (5, 12), (6, 11), (7, 8), (9, 10)],
  [(0, 3), (6, 5), (1, 15), (2, 14), (4, 13), (7, 8), (9, 10), (11, 12)],
  [(0, 3), (2, 6), (1, 15), (4, 14), (5, 13), (7, 8), (9, 10), (11, 12)]]

def rules : Array Price := #[
  ⟨#[1, 8], #[0, 0, 0, 2], #[-2, 0, 0, 0, 1, 1, 0, 0, 0], #[3, 7, 2, 6, 5, 5, 13, 4, 0, 1, 4, -1, 5, 0],
   #[87380, 87380, 87380, 87380, 87380, 87380, 87380, 87380, 87380, 87380, 87380, 87380, 87380, 87380, 87380, 87380, 87380, 87380, 87380, 87380, 87380, 87380, 87380, 87380, 87380, 87380, 87380, 87380, 87380, 87380, 87380, 87380, 87380, 87380, 87380, 87380, 87380, 87380, 87380, 87380, 87380, 87380, 87380]⟩,
  ⟨#[1, 8], #[0, 0, 2, 0], #[6, 0, 0, 0, 1, 1, 0, 0, 0], #[-1, 3, 0, 2, 1, 1, 7, 0, 0, 1, 6, -1, 7, 0],
   #[87365, 70997, 70997, 70997, 70997, 70997, 83285, 86357, 21845, 21845, 21845, 21845, 21845, 21845, 21845, 21845, 70997, 21845, 21845, 21845, 21845, 21845, 21845, 21845, 21845, 21845, 21845, 21845, 21845, 21845, 21845, 21845, 21845, 21845, 21845, 21845, 21845, 21845, 21845, 21845, 21845, 21845, 21845]⟩,
  ⟨#[4, 5], #[3, 3, 0, 0], #[6, 0, 0, 0, 0, 0, 4, 1, 1], #[5, 4, -2, 0, 0, 4, 12, 0, 1, 0, 6, 1, 6, 0],
   #[86021, 5141, 5441, 341, 341, 341, 1349, 341, 341, 341, 341, 341, 341, 341, 341, 341, 4181, 1109, 16469, 341, 4181, 20501, 1301, 341, 16469, 1301, 341, 16469, 1109, 5141, 1301, 341, 341, 4181, 16469, 1109, 5381, 341, 1349, 341, 341, 17669, 21824]⟩,
  ⟨#[2, 7], #[0, 0, 1, 2], #[0, 3, -1, 0, 0, 1, -1, 0, 1], #[1, 5, -1, 2, 1, 3, 10, 0, 0, 0, 3, -1, 4, -1],
   #[87376, 87376, 87376, 87376, 87376, 87376, 87376, 87376, 87376, 87376, 87376, 87376, 87376, 87376, 87376, 87376, 87376, 87376, 87376, 87376, 87376, 87376, 87376, 87376, 87376, 87376, 87376, 87376, 87376, 87376, 87376, 87376, 87376, 87376, 87376, 87376, 87376, 87376, 87376, 87376, 87376, 87376, 87376]⟩,
  ⟨#[3, 6], #[0, 0, 1, 2], #[0, 1, 1, 0, 0, -1, 3, 2, 1], #[4, 3, 0, -2, -1, 5, 7, 0, -1, -3, 1, 0, 0, -2],
   #[87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360]⟩,
  ⟨#[1, 3, 5], #[0, 0, 0, 0, 3, 3, 0, 0, 0, 3], #[1, -5, -2, 0, 0, 0, 0, 0, 0, 0, 4, 4, 4, 4, 4], #[7, 6, 0, -1, -1, 6, 11, -1, -5, -9, 0, -5, 0, -9],
   #[174661, 141973, 141973, 141973, 141973, 141973, 166549, 172693, 43669, 43669, 43429, 43669, 43669, 43669, 43669, 43669, 141973, 43669, 43669, 43669, 43669, 43669, 43669, 43669, 43669, 43669, 43669, 43669, 43669, 43669, 43669, 43669, 43669, 43669, 43669, 43669, 43669, 43669, 43669, 43669, 43669, 43669, 43669]⟩,
  ⟨#[2, 7], #[0, 3, 3, 0], #[10, 4, 0, 0, 0, 0, -2, 1, 1], #[1, 6, 0, -1, -1, 6, 14, -1, 1, 0, 9, 1, 9, 0],
   #[87301, 5461, 5461, 5461, 5461, 5461, 66901, 82261, 5461, 5461, 5461, 17749, 20821, 5461, 20821, 5461, 5461, 17749, 21589, 5461, 5461, 21781, 17749, 5461, 21589, 17749, 5461, 21589, 17749, 5461, 17749, 5461, 20821, 5461, 21589, 17749, 5461, 5461, 5461, 20821, 20821, 21829, 21844]⟩,
  ⟨#[3, 6], #[0, 0, 3, 12], #[0, 20, -2, 0, 0, 2, 0, -1, 4], #[18, 24, -2, 4, 2, 20, 47, 0, 12, 13, 20, 10, 22, 11],
   #[87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360, 87360]⟩,
  ⟨#[1, 3, 5], #[0, 0, 0, 5, 5, 5, 0, 0, 0, 5], #[10, 0, 7, 5, 5, 7, 0, 0, 2, 0, 0, 2, 0, 2, 4], #[-15, -10, -15, -10, -5, 0, 15, 0, -20, -15, 5, -15, 0, -10],
   #[174661, 141973, 141973, 141973, 141973, 141973, 166549, 172693, 43669, 43669, 43429, 43669, 43669, 43669, 43669, 43669, 141973, 43669, 43669, 43669, 43669, 43669, 43669, 43669, 43669, 43669, 43669, 43669, 43669, 43669, 43669, 43669, 43669, 43669, 43669, 43669, 43669, 43669, 43669, 43669, 43669, 43669, 43669]⟩,
  ⟨#[1, 3, 5], #[0, 0, 0, 10, 10, 10, 10, 10, 0, 0], #[10, 0, 2, 5, 5, 17, 0, 0, 12, 0, -10, 2, 0, 2, 14], #[-35, -15, -30, -10, -5, -5, 35, 0, -45, -30, 5, -40, 0, -25],
   #[173386, 76138, 76438, 71338, 71338, 71338, 84634, 86698, 22186, 22186, 22186, 22186, 22186, 22186, 22186, 22186, 75178, 22954, 38314, 22186, 26026, 42346, 23146, 22186, 38314, 23146, 22186, 38314, 22954, 26986, 23146, 22186, 22186, 26026, 38314, 22954, 27226, 22186, 23194, 22186, 22186, 39514, 43669]⟩,
  ⟨#[1, 3, 5], #[0, 0, 0, 10, 10, 10, 10, 5, 0, 0], #[20, 0, 2, 10, 10, 17, 0, 0, 7, 0, -5, 2, 0, 2, 9], #[-35, -20, -30, -20, -10, 0, 25, 0, -45, -30, 10, -35, 0, -20],
   #[173386, 76138, 76438, 71338, 71338, 71338, 84634, 86698, 22186, 22186, 22186, 22186, 22186, 22186, 22186, 22186, 75178, 22954, 38314, 22186, 26026, 42346, 23146, 22186, 38314, 23146, 22186, 38314, 22954, 26986, 23146, 22186, 22186, 26026, 38314, 22954, 27226, 22186, 23194, 22186, 22186, 39514, 43669]⟩,
  ⟨#[1, 2, 6], #[0, 0, 0, 0, 2, 2, 0, 0, 0, 2], #[5, 0, 3, 0, -1, 0, 1, 0, 1, 0, 0, 1, -1, 0, 1], #[1, 4, -1, 2, 1, 2, 9, 0, 0, 0, 5, -1, 6, -1],
   #[174725, 141989, 141989, 141989, 141989, 141989, 166565, 172709, 43685, 43685, 43685, 43685, 43685, 43685, 43685, 43685, 141989, 43685, 43685, 43685, 43685, 43685, 43685, 43685, 43685, 43685, 43685, 43685, 43685, 43685, 43685, 43685, 43685, 43685, 43685, 43685, 43685, 43685, 43685, 43685, 43685, 43685, 43685]⟩]

def group (v : Nat) := if v == 0 then 0 else if v ≤ 3 then 1 else 2
def roles (p : Endgame.Pairing) := #[
  Endgame.edgeCounts p 0 1, Endgame.edgeCounts p 0 2, Endgame.edgeCounts p 1 1,
  Endgame.edgeCounts p 1 2, Endgame.edgeCounts p 2 2]
def properExample (p : Endgame.Pairing) := p.length == 8 && p.all (fun e => e.1 != e.2 && e.1 < 16 && e.2 < 16) &&
  (List.range 16).all (fun v => (p.filter (fun (a,b) => v==a || v==b)).length == 1)
def pairTypes (n : Nat) := (Array.range n).flatMap fun i =>
  ((Array.range n).filter (fun j => i ≤ j)).map (fun j => (i,j))
def tripTypes (n : Nat) := (pairTypes n).flatMap fun (i,j) =>
  ((Array.range n).filter (fun k => j ≤ k)).map (fun k => (i,j,k))
def lookup2 (n : Nat) := (Array.range (n*n)).map fun k =>
  let a := k/n; let b := k%n
  (pairTypes n).toList.idxOf (min a b, max a b)
def lookup3 (n : Nat) := (Array.range (n*n*n)).map fun k =>
  let a := k/(n*n); let b := (k/n)%n; let c := k%n
  let lo := min a (min b c); let hi := max a (max b c)
  (tripTypes n).toList.idxOf (lo,a+b+c-lo-hi,hi)

def cell (code i : Nat) := (code >>> (2*i)) % 4
def assignments (sizes : Array Nat) : Nat → Array Nat
  | 0 => #[0]
  | k+1 => (Array.range sizes.size).flatMap fun j =>
    if sizes[j]! == 0 then #[] else
      (assignments (sizes.set! j (sizes[j]!-1)) k).map (fun code => (code <<< 2) ||| j)

def weight (r : Price) (tbl : Array Nat) (code : Nat) (t : Array Nat) :=
  let n := r.sizes.size
  r.weights[tbl[n*n*cell code t[0]! + n*cell code t[1]! + cell code t[2]!]!]!
def bid (r : Price) (tbl : Array Nat) (code : Nat) (e : Nat × Nat) : Int :=
  let (a,b) := e
  let n := r.sizes.size
  if b < 7 then 0 else if a < 7 then r.edge[n*group a+cell code (b-7)]!
  else r.edge[3*n + tbl[n*cell code (a-7)+cell code (b-7)]!]!
def pricesValid (r : Price) := Id.run do
  let n := r.sizes.size
  let t2 := lookup2 n
  let t3 := lookup3 n
  let all := assignments r.sizes 9
  for i in [:kinds.size] do
    let p := examples[i]!
    let blocked := (Endgame.blocked (Endgame.edgeSet p) Endgame.ordinaryA Endgame.ordinaryB).toArray.map
      (fun t => BlockCatalogue.points (t >>> 7))
    for code in all do
      let cost := p.foldl (fun sum e => sum + bid r t2 code e) r.color[i]!
      let loss := blocked.foldl (fun sum t => sum + weight r t3 code t) 0
      if cost < (loss : Int) then return false
  return true

def budget (r : Price) (row : Array Nat) := Id.run do
  let n := r.sizes.size
  let mut total : Int := 0
  for i in [:row.size] do total := total+(row[i]! : Int)*r.color[i]!
  for z in [:3] do
    for j in [:n] do
      let capacity := (if z==0 then 1 else 3)*r.sizes[j]!
      total := total+(capacity : Int)*r.edge[z*n+j]!
  let ps := pairTypes n
  for k in [:ps.size] do
    let (i,j) := ps[k]!
    let x := r.sizes[i]!; let y := r.sizes[j]!
    let count := if i==j then x*(x-1)/2 else x*y
    total := total+(count : Int)*r.edge[3*n+k]!
  return total

def small := BlockCatalogue.catalogue.filter (fun h => h.size ≤ 39)
def placements (r : Price) := Id.run do
  let table := lookup3 r.sizes.size
  let allowed := assignments r.sizes 9
  let mut out := #[]
  for i in [:small.size] do
    let code := r.witnesses[i]!
    if !allowed.contains code then return #[]
    out := out.push ((small[i]!).foldl (fun total t =>
      total + weight r table code (BlockCatalogue.points t)) 0)
  return out
def demands := rules.map placements

def use (remaining p : Array Nat) (count : Nat) :=
  (Array.range 5).all (fun i => p[i]!*count ≤ remaining[i]!)
def removeUsed (remaining p : Array Nat) (count : Nat) :=
  (Array.range 5).map (fun i => remaining[i]! - p[i]!*count)
def doubleTypes := (Array.range kinds.size).filter (fun i => kinds[i]!.toList.sum == 2)
def extra (p : Array Nat) :=
  (if p[0]!+p[1]! == 1 then 1 else 0) +
  (if p[3]! == 2 || (p[2]! == 1 && p[4]! == 1) then 3 else 0)
def totalRoles : Array Nat := #[3,3,3,9,3]
def singles := (Array.range 5).map fun i =>
  kinds.toList.idxOf ((Array.range 5).map (fun j => if i==j then 1 else 0))
def makeRows (remaining row : Array Nat) (nColors paid : Nat) : List Nat → Array (Array Nat)
  | [] => Id.run do
    let used := nColors+remaining.toList.sum
    if used > 15 then return #[]
    let mut result := row.set! 0 (15-used)
    for i in [:5] do result := result.set! singles[i]! remaining[i]!
    return #[result]
  | i::is => Id.run do
    let mut out := #[]
    let p := kinds[i]!
    for count in [:11] do
      if use remaining p count && paid+count*extra p ≤ 3 then
        out := out ++ makeRows (removeUsed remaining p count) (row.set! i count)
          (nColors+count) (paid+count*extra p) is
    return out
def rows := makeRows totalRoles (Array.replicate kinds.size 0) 0 0 doubleTypes.toList
def swapKind (p : Array Nat) := #[p[1]!,p[0]!,p[4]!,p[3]!,p[2]!]
def swapped (row : Array Nat) := kinds.map (fun p => row[kinds.toList.idxOf (swapKind p)]!)
def checkedRow (row : Array Nat) := Id.run do
  let a := rules.map (fun r => min (budget r row) (budget r (swapped row)))
  for i in [:small.size] do
    if !(Array.range rules.size).any (fun j =>
        demands[j]!.size == small.size && a[j]! < (demands[j]![i]! : Int)) then return false
  return true

theorem matching_types : (Endgame.rows 0).all (fun p =>
    !Endgame.valid (Endgame.edgeSet p) || kinds.contains (roles p)) = true ∧
    examples.zipIdx.all (fun (p,i) => properExample p && roles p == kinds[i]!) = true := by native_decide
theorem twelve_price_bounds : rules.all pricesValid = true := by native_decide
theorem every_cheap_profile : rows.all checkedRow = true ∧ small.size = 43 := by native_decide
#print axioms matching_types
#print axioms twelve_price_bounds
#print axioms every_cheap_profile
end Score39
