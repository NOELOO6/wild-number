import WeightedSurvivor
namespace FiveColors
set_option maxHeartbeats 0
set_option maxRecDepth 300000

def rows (s : String) : Array (Array Nat) :=
  ((s.trim.splitOn "\n").map fun line =>
    ((line.splitOn " ").filterMap String.toNat?).toArray).toArray

def colors := rows (include_str "colors.txt")
def layouts := rows (include_str "layouts.txt")
def prices := rows (include_str "prices.txt")
def bit (v : Nat) := 1 <<< v
def index (a b : Nat) := 16 * min a b + max a b

def validColor (m : Array Nat) : Bool := m.size == 16 && (Array.range 16).all fun v =>
  let j := m[v]!
  j < 16 && j != v && m[j]! == v

def knownEdge (a b : Nat) := colors.any fun m => m[a]! == b
def closeSide (m : Array Nat) (side : Nat) := (Array.range 16).all fun v =>
  side.testBit v == side.testBit m[v]!

def cuts (g : Array Nat) : Array Nat := Id.run do
  let mut a := #[]
  for j in [1:g.size] do
    a := a.push (g[j]! ||| bit 15)
    for k in [1:j] do a := a.push (g[j]! ||| g[k]!)
  return a

def validLayout (g : Array Nat) := g.size == 6 && g[0]! > 0 &&
  (g.extract 1 6).all (fun t => t < bit 15 && ((List.range 15).filter t.testBit).length == 3)
def allCovered (g : Array Nat) := (g.extract 1 6).foldl (· ||| ·) 0 == bit 15 - 1

def cutIndex : Array Nat := Id.run do
  let mut table := Array.replicate 65536 0
  for i in [0:layouts.size] do
    for s in cuts layouts[i]! do table := table.modify s (· ||| bit i)
  return table

def priceTable : Array Nat := Id.run do
  let mut table := Array.replicate 256 0
  for q in prices do table := table.modify (index q[0]! q[1]!) (· + q[2]!)
  return table

def weightTable : Array (Array Nat) := Id.run do
  let mut table := #[]
  for j in [0:(layouts.size+7)/8] do
    let mut w := #[0]
    for i in [0:8] do
      let v := (layouts[8*j+i]?.getD #[])[0]?.getD 0
      w := w ++ w.map (· + v)
    table := table.push w
  return table

def loss (m : Array Nat) : Nat := Id.run do
  let mut hits := 0
  for i in [0:m.size] do
    for j in [0:i] do
      let p := m[i]! ||| m[j]!
      hits := hits ||| cutIndex[p]!
      for k in [0:j] do hits := hits ||| cutIndex[p ||| m[k]!]!
  let mut val := 0
  for t in weightTable do
    val := val + t[hits &&& 255]!
    hits := hits >>> 8
  return val

/-- Counts residual perfect matchings which meet their price bound. -/
def tally : Nat → List Nat → Array Nat → Nat → Nat
  | 0, [], m, budget => if loss m ≤ budget then 1 else 0
  | k+1, a::rest, m, budget => (rest.map fun b =>
      if knownEdge a b then 0 else
        tally k (rest.erase b) (m.push (bit a ||| bit b))
          (budget + priceTable[index a b]!)).sum
  | _, _, _, _ => 0

def number : Nat → List Nat → Nat
  | 0, [] => 1
  | k+1, a::rest => (rest.map fun b =>
      if knownEdge a b then 0 else number k (rest.erase b)).sum
  | _, _ => 0

theorem supplied_colors_and_layouts :
    colors.size = 5 ∧ colors.all validColor = true ∧
    (Array.range 16).all (fun v => ((colors.map (fun m => m[v]!)).toList.eraseDups).length == 5) = true ∧
    layouts.all (fun g => validLayout g && allCovered g &&
      (cuts g).all (fun s => !(colors.any fun m => closeSide m s))) = true ∧
    prices.all (fun q => q.size == 3 && q[0]! < q[1]! && q[1]! < 16 &&
      !knownEdge q[0]! q[1]!) = true ∧
    (layouts.map (fun g => g[0]!)).toList.sum = 99996 ∧ priceTable.toList.sum = 99469 := by
  native_decide

theorem every_remaining_matching :
    tally 8 (List.range 16) #[] 0 = number 8 (List.range 16) ∧
    number 8 (List.range 16) = 91446 := by native_decide
#print axioms weighted_survivor
#print axioms supplied_colors_and_layouts
#print axioms every_remaining_matching
end FiveColors
