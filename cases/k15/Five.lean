import Teams
/- A rotation through one fifth of a turn on a properly colored K16.
   The selected root is fixed. A layout is five triples on its complement. -/
namespace Five
open Teams
set_option maxHeartbeats 0
set_option maxRecDepth 150000

def pts := List.range 16
def points (s : Nat) := pts.filter s.testBit
def span (xs : List Nat) := xs.foldl (fun s v => s ||| bit v) 0
def goodGrouping (root : Nat) (g : Grouping) := g.length == 5 &&
  g.all (fun s => s < 65536 && (points s).length == 3) &&
  g.foldl (· ||| ·) 0 == (65535 ^^^ bit root)
def cutList (root : Nat) (g : Grouping) := g.map (· ||| bit root) ++ unorderedPairs g (· ||| ·)
def step (fixedCount k v : Nat) := if v < fixedCount then v else
  fixedCount+5*((v-fixedCount)/5)+(v-fixedCount+k)%5
def turn (f : Nat → Nat) (s : Nat) := span ((points s).map f)

def cutTable (root : Nat) (layouts : Array Grouping) (rotations : List (Nat → Nat)) := Id.run do
  let mut table := Array.replicate 65536 0
  for (gs,i) in layouts.zipIdx do
    for f in rotations do
      for s in cutList root gs do
        let t := turn f s
        table := table.modify t (fun v => v ||| bit i)
  return table

def blocked (table : Array Nat) (m : Matching) :=
  (closedSides m).foldl (fun lost s => lost ||| table[s]!) 0
structure Starter where
  mask : Nat
  pairs : Matching
deriving Inhabited

def enumerate (orbit : Nat → Nat → Nat) (endTag : Nat) : Nat → List Nat → Starter → List Starter
  | 0, [], s => [s]
  | k+1, a::as, s => as.flatMap fun b =>
    let t := orbit a b
    if t >= endTag || s.mask.testBit t then [] else
      enumerate orbit endTag k (as.erase b) ⟨s.mask ||| bit t, pair a b :: s.pairs⟩
  | _, _, _ => []

/-- Three five-point rings, plus fixed root 15. -/
def triples3 := ((List.range 5).flatMap fun a => (List.range 5).map fun b =>
  (List.range 5).map fun i => span [i,5+(i+a)%5,10+(i+b)%5]).toArray
def orbit3 (a b : Nat) :=
  let i := a/5; let j := b/5; let d := (b%5+5-a%5)%5
  if b==15 then 21+i else if i==j then 2*i+min d (5-d)-1 else
    6+5*(if i==0 then j-1 else 2)+d
def ringStars (k : Nat) := enumerate orbit3 24 7 ((List.range 15).erase (5*k))
  ⟨bit (21+k),[pair (5*k) 15]⟩
def table3 := cutTable 15 triples3 [id]
def internal (s : Starter) := ((List.range 6).filter s.mask.testBit).length
def price : Array Nat := #[7,9,6,5,5,1,1]
def singleCheck (s : Starter) := internal s < 7 &&
  ((List.range 25).filter (blocked table3 s.pairs).testBit).length ≤ price[internal s]!
def rot3 (v : Nat) := if v==15 then 15 else 5*(v/5)+(v+1)%5

theorem layouts3 : triples3.size = 25 ∧ triples3.toList.Nodup ∧ triples3.all
    (fun g => goodGrouping 15 g && g.all (fun t => g.contains (turn rot3 t))) = true := by native_decide
theorem single_bound : (List.range 3).all (fun k =>
  (ringStars k).length == 50590 && (ringStars k).all singleCheck) = true := by native_decide
theorem three_prices : (List.range 7).all (fun i => (List.range 7).all
    (fun j => (List.range 7).all (fun k => i+j+k != 6 ||
      price[i]!+price[j]!+price[k]! ≤ 23))) = true := by decide

structure Entry where
  tag : Nat
  lost : Nat
  number : Nat
deriving Inhabited
def asEntry (s : Starter) : Entry :=
  let lost := blocked table3 s.pairs
  ⟨s.mask % (1 <<< 21),lost,((List.range 25).filter lost.testBit).length⟩
def lastRing := ((ringStars 2).map asEntry).foldl
  (fun (bs : Array (List Entry)) s => bs.modify s.tag (s :: ·))
  (Array.replicate (1 <<< 21) [])
def middle := ((ringStars 1).map asEntry).toArray
def whenExpensive := ((ringStars 0).map asEntry).all fun a =>
  a.number < 7 || middle.all (fun b => (a.tag &&& b.tag) != 0 ||
    (lastRing[2097151 ^^^ (a.tag ||| b.tag)]!).all (fun c =>
      a.number+b.number+c.number ≤ 19 ||
      ((List.range 25).filter (a.lost ||| b.lost ||| c.lost).testBit).length ≤ 19))
theorem six_survive : whenExpensive = true := by native_decide

/-- Six fixed points, numbered 0 through 5, plus two five-point rings. -/
def triples2 : Array Grouping := #[
  [32840, 5632, 10256, 16418, 388],
  [4144, 32774, 200, 17664, 10752],
  [33152, 3136, 4102, 16928, 8216],
  [1030, 33040, 12320, 648, 18496],
  [16648, 4144, 32834, 2688, 9220],
  [34048, 194, 4136, 16404, 10752],
  [10496, 36928, 176, 17410, 524],
  [2088, 4114, 49408, 1156, 8768],
  [16528, 3584, 32804, 8202, 4416],
  [7168, 84, 32808, 24832, 642],
  [33408, 280, 8198, 7168, 16480],
  [36866, 8576, 17472, 2096, 524],
  [3088, 268, 546, 12352, 49280],
  [2192, 16418, 4108, 1792, 41024],
  [1030, 34880, 12296, 176, 17152],
  [4116, 416, 16456, 33282, 11264],
  [24578, 3080, 4480, 32804, 592],
  [35072, 1044, 4610, 8384, 16424],
  [648, 4114, 25600, 292, 34880],
  [580, 37888, 8210, 2432, 16424],
  [1312, 4736, 32792, 2054, 24640],
  [2068, 12416, 1568, 33088, 16394],
  [100, 37888, 24578, 280, 2688],
  [41088, 4132, 19456, 74, 784],
  [41216, 2192, 546, 21504, 76],
  [32808, 20608, 8210, 2308, 1600],
  [3584, 4480, 16408, 8258, 32804],
  [6208, 146, 524, 41984, 16672],
  [36992, 3584, 8216, 100, 16642],
  [34832, 98, 24832, 1664, 4108],
  [51200, 4162, 1072, 8712, 388],
  [33288, 8212, 2082, 1216, 20736]]
def orbit2 (a b : Nat) := if b<6 then 16 else if a<6 then 2*a+(if b>=11 then 1 else 0)
  else if (a-6)/5 != (b-6)/5 then 16 else
    12+2*((a-6)/5)+min (b-a) (5-(b-a))-1
def movingStars (k : Nat) := enumerate orbit2 16 7 ((List.range' 1 15).erase (6+5*k))
  ⟨bit k,[pair 0 (6+5*k)]⟩
def possibleFixed := (List.range 5).flatMap fun s =>
  let cross := (List.range 5).map fun i => pair (6+i) (11+(i+s)%5)
  (matchings 2 ((List.range' 1 5).erase (1+s))).map fun p =>
    pair 0 (1+s) :: p ++ cross
def tableFixed := cutTable 0 triples2 [id]
def table2 := cutTable 0 triples2 ((List.range 5).map (step 6))
def allLayouts := (1 <<< triples2.size)-1
def winning (s : Starter) := allLayouts ^^^ blocked table2 s.pairs
def byMask := (movingStars 1).foldl (fun (bs : Array (List Nat)) s =>
    bs.modify s.mask (winning s :: ·)) (Array.replicate 65536 [])
def completeCheck := (movingStars 0).all fun s =>
  let good := winning s
  (byMask[65535 ^^^ s.mask]!).all (fun other => (good &&& other) != 0)
def pairCount := ((movingStars 0).map (fun s => (byMask[65535 ^^^ s.mask]!).length)).sum

theorem fixed_colors : triples2.size = 32 ∧ triples2.all (goodGrouping 0) = true ∧
    possibleFixed.length = 15 ∧ possibleFixed.all (fun m => blocked tableFixed m == 0) = true := by native_decide
theorem all_pairs : (movingStars 0).length = 7920 ∧ (movingStars 1).length = 7920 ∧
    pairCount = 1382400 ∧ completeCheck = true := by native_decide

#print axioms single_bound
#print axioms three_prices
#print axioms all_pairs
end Five
