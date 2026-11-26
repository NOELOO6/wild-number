import Std
namespace FourColors
set_option maxHeartbeats 0
set_option maxRecDepth 300000

abbrev Row := Array Nat
def rows (s : String) : Array Row := ((s.trim.splitOn "\n").map
  (fun x => ((x.splitOn " ").filterMap String.toNat?).toArray)).toArray
def bit (x : Nat) := 1 <<< x
def points := List.range 16
def size (s : Nat) := (points.filter s.testBit).length
def masks (d : Nat) := (Array.range 65536).filter (fun s => size s == d)
def indices (d : Nat) : Row := Id.run do
  let mut out := Array.replicate 65536 0
  let mut i := 0
  for s in masks d do
    out := out.set! s i
    i := i+1
  return out
def four := indices 4
def six := indices 6
def pos (q a b : Nat) := 5005 * four[q]! + six[min a b]!
def pairId (a b : Nat) := 16 * min a b + max a b
structure Tables where
  cuts : Row
  pieces : Row
  weight : Nat
 deriving Inhabited
def imageMask (p : Row) (x t : Nat) :=
  points.foldl (fun a i => if x.testBit i then a ||| bit (p[i]! ^^^ t) else a) 0
def genuine (s : Row) := s.size == 6 && s[0]! > 0 &&
  (s.extract 1 6).all (fun t => t < bit 15 && size t == 3) &&
  (s.extract 1 6).foldl (· ||| ·) 0 == 32767
def permutations (p : Row) := p.size == 16 && p.all (· < 16) && p.toList.eraseDups.length == 16
def tables (seeds perms : Array Row) (translations : Nat) : Tables := Id.run do
  let mut counts := Array.replicate 65536 0
  let mut splits := Array.replicate (1820*5005) 0
  let mut sum := 0
  for seed in seeds do
    let w := seed[0]!
    for p in perms do
      for shift in [0:translations] do
        let g := (seed.extract 1 6).map (fun t => imageMask p t shift)
        let root := bit (p[15]! ^^^ shift)
        sum := sum + w
        for i in [0:5] do
          let q := root ||| g[i]!
          counts := counts.modify q (· + w)
          for j in [0:i] do counts := counts.modify (g[i]! ||| g[j]!) (· + w)
          let other := (Array.range 5).filter (· != i)
          for j in [1:4] do
            let a := g[other[0]!]! ||| g[other[j]!]!
            splits := splits.modify (pos q a (65535 ^^^ q ^^^ a)) (· + w)
  return ⟨counts,splits,sum⟩

def pairs := ((List.range 256).filter (fun i => size i == 2)).toArray
def triples := ((List.range 256).filter (fun i => size i == 3)).toArray
def parts := pairs.map fun q => triples.filter fun a => a &&& q == 0 && a < (255 ^^^ q ^^^ a)
def vertexSides (m : Row) : Row := Id.run do
  let mut s := #[0]
  for e in m do s := s ++ s.map (· ||| e)
  return s
/-- A matching closes zero, one or three of the fifteen cuts of a layout.
    A three-cut hit corresponds to its unique partition into 4,6,6. -/
def fits (t : Tables) (m : Row) (price : Nat) : Bool := Id.run do
  let side := vertexSides m
  let mut total := 0
  let mut overlaps := 0
  for i in [0:pairs.size] do
    let q := side[pairs[i]!]!
    total := total + t.cuts[q]!
    for a in parts[i]! do
      let h := side[a]!
      overlaps := overlaps + t.pieces[pos q h (65535 ^^^ h ^^^ q)]!
  for b in triples do total := total + t.cuts[side[b]!]!
  return total ≤ price + 2*overlaps

def priceTable (ps : Array Row) : Row := Id.run do
  let mut p := Array.replicate 256 0
  for r in ps do p := p.modify (pairId r[0]! r[1]!) (· + r[2]!)
  return p
def enumerate (t : Tables) (d p : Row) : Nat → List Nat → Row → Nat → Nat × Nat
  | 0, [], m, cost => (1,if fits t m cost then 1 else 0)
  | n+1, a::vs, m, cost => vs.foldl (fun (r : Nat × Nat) b =>
      if d.contains (a ^^^ b) then r else
      let v := enumerate t d p n (vs.erase b) (m.push (bit a ||| bit b)) (cost+p[pairId a b]!)
      (r.1+v.1, r.2+v.2)) (0,0)
  | _, _, _, _ => (0,0)
def check (seeds perm ps : Array Row) (d : Row) (translations number : Nat) := Id.run do
  let t := tables seeds perm translations
  let p := priceTable ps
  let fixed := d.all fun k => fits t ((points.filter fun i => i < (i ^^^ k)).toArray.map
    (fun i => bit i ||| bit (i ^^^ k))) 0
  return seeds.all genuine && perm.all permutations && fixed &&
    ps.all (fun a => a.size == 3 && a[0]! < a[1]! && a[1]! < 16 && !d.contains (a[0]! ^^^ a[1]!)) &&
    p.toList.sum < t.weight && enumerate t d p 8 points #[] 0 == (number,number)

theorem four_binary_coordinates : check (rows (include_str "1-seeds.txt")) (rows (include_str "1-perms.txt"))
    (rows (include_str "1-prices.txt")) #[1,2,4,8] 16 187249 = true := by native_decide

theorem four_in_each_half : check (rows (include_str "0-seeds.txt")) (rows (include_str "0-perms.txt"))
    (rows (include_str "0-prices.txt")) #[1,2,3,4] 16 190289 = true := by native_decide

#print axioms four_binary_coordinates
#print axioms four_in_each_half
end FourColors
