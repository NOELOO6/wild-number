import Std

/- Rotating two heptagons gives seven colors from each of two starters.
   Edges and cuts are represented by bit sets. A template succeeds when
   each color crosses each nontrivial cut of its five wild components. -/
namespace Seven
set_option maxHeartbeats 0
set_option maxRecDepth 200000

abbrev Pattern := List Nat
def patterns : Array Pattern := #[
  [385, 1540, 4144, 18496, 8202],
  [4136, 17412, 2688, 8272, 259],
  [259, 28, 17024, 10304, 5152],
  [131, 8480, 2068, 16960, 5128],
  [1064, 10752, 20544, 274, 133],
  [8768, 261, 16424, 2192, 5122],
  [1288, 16897, 8384, 38, 6160],
  [1096, 274, 8705, 4228, 18464],
  [2084, 4168, 8576, 16897, 1042],
  [24704, 770, 4192, 13, 3088],
  [1296, 2177, 8232, 580, 20482],
  [2084, 1168, 8258, 521, 20736],
  [2096, 1034, 580, 12416, 16641],
  [133, 1064, 6208, 17152, 8210],
  [196, 274, 18464, 4609, 9224],
  [2072, 8450, 17920, 69, 4256],
  [580, 6176, 19, 392, 25600],
  [4136, 388, 1538, 18433, 8272],
  [4101, 656, 2306, 16480, 9224],
  [41, 4736, 82, 24832, 3076],
  [70, 10241, 17664, 648, 4144],
  [16390, 9280, 56, 6400, 641],
  [104, 1282, 4609, 24592, 2180],
  [1153, 328, 2096, 16898, 12292],
  [2065, 8288, 20736, 1154, 524],
  [8228, 16528, 1033, 6208, 770],
  [18436, 4384, 1104, 137, 8706],
  [17472, 2072, 4129, 8960, 134],
  [3088, 4192, 265, 17024, 8198],
  [28, 1282, 97, 2688, 28672],
  [1029, 6656, 8450, 16456, 176],
  [4609, 1160, 352, 24580, 2066],
  [2053, 8768, 304, 138, 21504],
  [2082, 4240, 16904, 1281, 8260],
  [8209, 16420, 4354, 2568, 1216],
  [1344, 648, 10242, 4129, 16404],
  [328, 8228, 1537, 18560, 4114],
  [1090, 14336, 16420, 536, 385],
  [52, 8768, 16768, 4099, 3080],
  [1064, 16641, 10304, 4240, 518],
  [262, 6656, 49, 17536, 8264],
  [12290, 1096, 2068, 385, 16928],
  [8201, 290, 6208, 644, 17424],
  [4105, 16480, 3088, 642, 8452],
  [21, 4232, 8450, 17440, 2624],
  [1033, 4356, 16418, 704, 10256],
  [4225, 8240, 16898, 1284, 2120],
  [112, 386, 20488, 8197, 3584],
  [20484, 1072, 131, 10496, 584],
  [1568, 28672, 2308, 88, 131],
  [4176, 8321, 2568, 1058, 16644],
  [18496, 8204, 50, 1792, 4225],
  [41, 16404, 9280, 6272, 770],
  [2065, 20482, 8708, 1312, 200],
  [400, 8736, 16390, 5128, 2113],
  [18944, 1044, 131, 8288, 4360],
  [772, 18496, 168, 8209, 5122],
  [8321, 16928, 5128, 2114, 276],
  [8512, 648, 16402, 37, 7168],
  [10248, 4129, 17920, 208, 262],
  [1044, 6272, 16450, 8201, 800],
  [224, 24584, 2561, 5124, 274],
  [2177, 20496, 1092, 296, 8706],
  [6176, 392, 577, 17410, 8212],
  [16898, 3076, 56, 4416, 8321],
  [2084, 24578, 4161, 152, 1792],
  [13312, 164, 265, 2624, 16402],
  [16960, 9217, 56, 388, 6146],
  [2592, 12304, 196, 266, 17409],
  [4164, 289, 8216, 17024, 3074],
  [5632, 73, 2178, 8452, 16432]]
def pts := List.range 15
def rot (v n : Nat) := if v < 14 then (v/7)*7 + (v+n)%7 else v
def idx (a b : Nat) := let m := max a b; m*(m-1)/2 + min a b
def maskEdge (a b : Nat) := 1 <<< idx a b
def crossing (s n : Nat) := pts.foldl (fun acc b => (List.range b).foldl (fun u a =>
  if s.testBit (rot a n) != s.testBit (rot b n) then u ||| maskEdge a b else u) acc) 0
def sides (gs : Pattern) := gs ++ (gs.zipIdx.flatMap fun (s,i) => (gs.take i).map (s ||| ·))
def translatedCuts := patterns.map fun gs =>
  ((sides gs).flatMap fun s => (List.range 7).map (crossing s)).eraseDups
def fixed := (List.range 7).foldl (fun z i => z ||| maskEdge i (7+i)) 0
def crosses (edges cut : Nat) := (edges &&& cut) != 0
def works (es p : Nat) := (translatedCuts[p]!).all (crosses es)

theorem valid_patterns : patterns.size = 71 ∧ patterns.all (fun gs =>
  gs.length == 5 && gs.all (fun g => g < 32768 && (pts.filter g.testBit).length == 3) &&
  pts.all (fun v => gs.any (fun g => g.testBit v))) = true := by native_decide

theorem fixed_works : (List.range patterns.size).all (works fixed) = true := by native_decide

/-- The orbit of a nonreserved edge. Tag 16 means that the aligned fixed
    matching already uses the edge. Inputs obey a < b. -/
def orbit (a b : Nat) :=
  if (a == 14 && b == 15) || (a < 7 && b == a+7) then 16
  else if b ≥ 14 then 12 + 2*(b-14) + a/7
  else if a/7 == b/7 then 3*(a/7) + min (b-a) (7-(b-a))-1
  else 5+(b-a)%7

structure Base where
  tag : Nat
  edges : Nat
deriving DecidableEq, Repr

def extend (b : Base) (x y : Nat) : Base :=
  ⟨b.tag ||| (1 <<< orbit x y), b.edges ||| maskEdge x y⟩

/-- Pair the first available vertex with one of the other available vertices.
    Distinct orbit tags are forced by edge-disjointness of the seven translates. -/
def enumerate : Nat → List Nat → Base → List Base
  | 0, [], b => [b]
  | k+1, x::xs, b => xs.flatMap fun y =>
      if orbit x y < 16 && !b.tag.testBit (orbit x y)
      then enumerate k (xs.erase y) (extend b x y) else []
  | _, _, _ => []

inductive Admissible : Nat → List Nat → Base → Base → Prop
  | done (b) : Admissible 0 [] b b
  | step {k x xs b z} (y) (inList : y ∈ xs)
      (tagFree : (orbit x y < 16 && !b.tag.testBit (orbit x y)) = true)
      (tail : Admissible k (xs.erase y) (extend b x y) z) : Admissible (k+1) (x::xs) b z

theorem enumerates {k vs b z} (h : Admissible k vs b z) : z ∈ enumerate k vs b := by
  induction h with
  | done b => simp [enumerate]
  | step y hy ok _ ih => exact List.mem_flatMap.mpr ⟨y,hy,by simpa [ok] using ih⟩

def remaining (root : Nat) := pts.erase root
def start (root : Nat) : Base := ⟨1 <<< orbit root 15, 0⟩
def bases (root : Nat) := enumerate 7 (remaining root) (start root)
def IsBase (root : Nat) (b : Base) := Admissible 7 (remaining root) (start root) b

def ids := List.range patterns.size
def wins (b : Base) := ids.filter (works b.edges)

structure Entry where
  base : Base
  solutions : List Nat
deriving DecidableEq

def makeEntry (b : Base) : Entry := ⟨b, wins b⟩
def bs := (bases 7).map makeEntry
def buckets : Array (List Entry) := bs.foldl (fun tbl b =>
  tbl.modify b.base.tag (b :: ·)) (Array.replicate 65536 [])
def as := (bases 0).map makeEntry

theorem all_bucketed : bs.all (fun b => (buckets[b.base.tag]!).contains b) = true := by native_decide
theorem counts : as.length = 19876 ∧ bs.length = 19876 ∧
    (as.foldl (fun n a => n+(buckets[65535 ^^^ a.base.tag]!).length) 0) = 797448 := by native_decide

theorem all_covered : as.all (fun a => (buckets[65535 ^^^ a.base.tag]!).all (fun b =>
  a.solutions.any b.solutions.contains)) = true := by native_decide

theorem all_starters (a b : Base) (ha : IsBase 0 a) (hb : IsBase 7 b)
    (complementary : 65535 ^^^ a.tag = b.tag) :
    ∃ p ∈ ids, works fixed p = true ∧ works a.edges p = true ∧ works b.edges p = true := by
  have ma : makeEntry a ∈ as := List.mem_map.mpr ⟨a,enumerates ha,rfl⟩
  have mb : makeEntry b ∈ bs := List.mem_map.mpr ⟨b,enumerates hb,rfl⟩
  have inBucket := List.all_eq_true.mp all_bucketed _ mb
  have h := List.all_eq_true.mp all_covered _ ma
  change (buckets[65535 ^^^ a.tag]!).all _ = true at h
  rw [complementary] at h
  have member : makeEntry b ∈ (buckets[b.tag]!) := by
    exact List.contains_iff_mem.mp inBucket
  obtain ⟨p,pa,pb⟩ := List.any_eq_true.mp (List.all_eq_true.mp h _ member)
  have left := List.mem_filter.mp (show p ∈ wins a from pa)
  have right := List.mem_filter.mp (show p ∈ wins b from List.contains_iff_mem.mp pb)
  exact ⟨p,left.1,List.all_eq_true.mp fixed_works _ left.1,left.2,right.2⟩

#print axioms all_starters
end Seven
