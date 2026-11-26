import Teams
/- Finite profile certificates for the nine remaining points.
   The integer prices bound a weighted count for each individual matching.
   Adding them across colors uses each edge of the complete graph once. -/
namespace Endgame
open Teams
set_option maxHeartbeats 0
set_option maxRecDepth 200000

structure Rule where
  size : Nat
  w : Array Nat
  limit : Nat
  denominator : Nat
  price : Array Int
deriving Repr

def rules38 : List Rule := [
  ⟨1, #[0, 1, 0, 0], 24, 1, #[0, -1, 0, 1, -2, -8, -1, 0, -1, -6, 1, 0, 0, 0, 0, 3]⟩,
  ⟨4, #[0, 0, 1, 1], 29, 15, #[0, 0, 0, -10, -32, -20, 10, 0, 3, -20, 0, 3, 0, -7, -4, 20]⟩,
  ⟨7, #[0, 0, 0, 1], 30, 2, #[0, 0, 0, -4, -7, -6, 0, 0, 0, -6, 0, 0, 0, -1, 0, 4]⟩,
  ⟨1, #[1, 0, 0, 0], 31, 1, #[0, 0, 0, -1, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1]⟩]
def rules40 : List Rule := [
  ⟨1, #[0, 1, 0, 0], 24, 3, #[-2, 2, -2, 0, 1, 10, 0, 1, -2, 0, 1, 2, -2, 2, -2, 12, 6, 0, 0, 1, 1, 0, -3, 0]⟩,
  ⟨2, #[1, 0, 0, 0], 29, 2, #[0, 3, 0, 0, -1, 1, 0, -1, 2, 5, -1, -2, 0, 3, 0, -4, 0, 0, 1, -1, 0, 0, 0, 2]⟩,
  ⟨4, #[0, 0, 1, 1], 30, 1, #[0, 2, 0, 1, 1, 3, 1, 1, 1, 2, 1, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0]⟩,
  ⟨1, #[1, 0, 0, 0], 33, 7, #[-9, 7, -9, -2, -14, 0, -5, 0, -9, 3, -14, -12, -9, 7, -9, 0, 7, -2, -2, 0, 0, 0, 3, 10]⟩,
  ⟨4, #[1, 1, 0, 0], 37, 7, #[2, 21, 2, -5, -21, 0, 5, 0, -5, 11, -21, -16, 2, 21, 2, 0, 0, -5, -5, 0, 0, 11, 11, 11]⟩,
  ⟨4, #[1, 0, 1, 0], 39, 9, #[-4, 23, -4, -13, -27, -6, 0, -13, 0, 23, -27, -27, -4, 23, -4, 0, -6, 0, 0, 0, 0, 14, 11, 14]⟩,
  ⟨3, #[0, 2, 3, 1], 96, 1, #[-5, 0, -5, 1, 2, 9, -1, 0, 1, 2, 2, 1, -5, 0, -5, 9, 7, 1, 1, 0, 0, 1, 0, 0]⟩]

def zone := 127
def outside := 65408
def actualA := 52
def ordinaryA := 14
def ordinaryB := 112
def actualB := 74
def triples := ((List.range 512).filter
  (fun s => ((List.range 9).filter s.testBit).length == 3)).map (fun s => s <<< 7)
def closedAt (m : Matching) (s : Nat) :=
  m.all (fun e => (e &&& s) == 0 || (e &&& s) == e)
def blocked (m : Matching) (a b : Nat) := triples.filter (fun x =>
  closedAt m (1 ||| x) || closedAt m (outside ^^^ x) ||
  closedAt m (a ||| x) || closedAt m (b ||| x))
def number (s : Nat) := ((List.range 16).filter s.testBit).length
def weighted (r : Rule) (w : Nat) (xs : List Nat) :=
  (xs.map (fun s => r.w[number (s &&& w)]!)).sum

/-- The five groups are the specified point, the two triples in its seven,
    and the two parts of the other nine. -/
def kind (size v : Nat) :=
  if v == 0 then 0 else if v ≤ 3 then 1 else if v ≤ 6 then 2
  else if v < 7+size then 3 else 4
def typeIndex (a b : Nat) :=
  let lo := min a b
  ([0,5,9,12,14] : List Nat)[lo]! + max a b-lo
def priceFor (r : Rule) (x y : Nat) :=
  r.price[typeIndex (kind r.size x) (kind r.size y)]!
def edges := (List.range 16).flatMap (fun j => (List.range j).map (fun i => (i,j)))
def allPrices (r : Rule) := (edges.map (fun (x,y) => priceFor r x y)).sum + 38*r.price[15]!

abbrev Pairing := List (Nat × Nat)
def edgeSet (p : Pairing) := p.map (fun (x,y) => pair x y)
def valid (m : Matching) :=
  (m.filter (fun e => (e &&& zone) == e)).length ≤ 2 &&
    !closedAt m 15 && !closedAt m 113 && !closedAt m 126
def priceBound (r : Rule) (p : Pairing) :=
  let m := edgeSet p
  let xs := blocked m ordinaryA ordinaryB
  let w := ((1 <<< r.size)-1) <<< 7
  !(valid m) || decide (((r.denominator * weighted r w xs : Nat) : Int) ≤
    (p.map (fun (x,y) => priceFor r x y)).sum + r.price[15]! * (xs.length : Int))

/-- Keep one possible partner per vertex group at each step. Exchanging two
    unused vertices in a group leaves all the quantities in priceBound unchanged. -/
def partners (t : Nat) (xs : List Nat) :=
  (List.range 5).filterMap (fun g => xs.find? (fun x => kind t x == g))
def profiles (t : Nat) : Nat → List Nat → Pairing → List Pairing
  | 0, [], p => [p]
  | k+1, x::xs, p => (partners t xs).flatMap (fun y =>
       profiles t k (xs.erase y) ((x,y)::p))
  | _, _, _ => []
def rows (size : Nat) := profiles size 8 (List.range 16) []

theorem all_matching_profiles : rules38.all (fun r =>
    (rows r.size).all (priceBound r) && 0 ≤ r.price[15]! &&
    allPrices r < (r.denominator*(r.limit+1) : Nat)) = true := by native_decide

def edgeCounts (p : Pairing) (a b : Nat) :=
  (p.filter (fun (x,y) => min (kind 0 x) (kind 0 y) == a &&
    max (kind 0 x) (kind 0 y) == b)).length

/-- The number of obstruction occurrences can be read from the seven alone.
    A double color has two pairs in the seven. h counts those touching the root.
    j counts double colors whose four endpoints meet each triple twice. -/
def costIdentity (p : Pairing) :=
  let m := edgeSet p
  let roots := edgeCounts p 0 1 + edgeCounts p 0 2
  let aa := edgeCounts p 1 1
  let ab := edgeCounts p 1 2
  let bb := edgeCounts p 2 2
  let h := if roots == 1 && aa+ab+bb == 1 then 1 else 0
  let j := if ab == 2 || (aa == 1 && bb == 1) then 1 else 0
  !(valid m) || ((blocked m ordinaryA ordinaryB).length + 2*roots + ab ==
    3 + 2*(aa+bb) + h + 3*j)

theorem seven_point_cost : (rows 0).all costIdentity = true := by native_decide

/-- These are the internal pairs in the explicit seven-point coloring.
    Other endpoints are assigned canonical distinct labels outside the seven. -/
def canonical : List Pairing := [
  [(3, 4), (0, 15), (1, 14), (2, 13), (5, 12), (6, 11), (7, 8), (9, 10)],
  [(1, 6), (0, 15), (2, 14), (3, 13), (4, 12), (5, 11), (7, 8), (9, 10)],
  [(1, 4), (0, 15), (2, 14), (3, 13), (5, 12), (6, 11), (7, 8), (9, 10)],
  [(0, 2), (1, 15), (3, 14), (4, 13), (5, 12), (6, 11), (7, 8), (9, 10)],
  [(0, 5), (2, 6), (1, 15), (3, 14), (4, 13), (7, 8), (9, 10), (11, 12)],
  [(0, 1), (2, 5), (3, 15), (4, 14), (6, 13), (7, 8), (9, 10), (11, 12)],
  [(1, 3), (4, 6), (0, 15), (2, 14), (5, 13), (7, 8), (9, 10), (11, 12)],
  [(0, 3), (1, 15), (2, 14), (4, 13), (5, 12), (6, 11), (7, 8), (9, 10)],
  [(1, 5), (2, 4), (0, 15), (3, 14), (6, 13), (7, 8), (9, 10), (11, 12)],
  [(4, 5), (0, 15), (1, 14), (2, 13), (3, 12), (6, 11), (7, 8), (9, 10)],
  [(0, 4), (3, 5), (1, 15), (2, 14), (6, 13), (7, 8), (9, 10), (11, 12)],
  [(0, 6), (1, 2), (3, 15), (4, 14), (5, 13), (7, 8), (9, 10), (11, 12)],
  [(2, 3), (0, 15), (1, 14), (4, 13), (5, 12), (6, 11), (7, 8), (9, 10)],
  [(3, 6), (0, 15), (1, 14), (2, 13), (4, 12), (5, 11), (7, 8), (9, 10)],
  [(5, 6), (0, 15), (1, 14), (2, 13), (3, 12), (4, 11), (7, 8), (9, 10)]]
def crossesPrice (r : Rule) (w z y : Nat) :=
  let group := if z == 0 then 0 else if actualA.testBit z then 1 else 2
  r.price[15+2*group+(if w.testBit y then 0 else 1)]!
def outerPrice (r : Rule) (w x y : Nat) :=
  r.price[21+(if w.testBit x then 0 else 1)+(if w.testBit y then 0 else 1)]!
def bid (r : Rule) (w : Nat) (e : Nat × Nat) :=
  if e.2 < 7 then 0 else if e.1 < 7 then crossesPrice r w e.1 e.2 else outerPrice r w e.1 e.2
def outsideSets (k : Nat) := ((List.range 512).filter (fun s => number s == k)).map (· <<< 7)
def fixedPrice (r : Rule) (w : Nat) :=
  ((List.range 15).map (fun i => r.price[i]!)).sum + (edges.map (bid r w)).sum

theorem forty_occurrences :
    (canonical.map (fun p => (blocked (edgeSet p) actualA actualB).length)).sum = 40 := by native_decide
theorem partial_prices : rules40.all (fun r =>
  (outsideSets r.size).all (fun w =>
    fixedPrice r w < (r.denominator*(r.limit+1) : Nat) &&
    canonical.zipIdx.all (fun (p,c) =>
      ((r.denominator * weighted r w (blocked (edgeSet p) actualA actualB) : Nat) : Int)
        ≤ r.price[c]! + (p.map (bid r w)).sum))) = true := by native_decide
#print axioms all_matching_profiles
#print axioms partial_prices
end Endgame
