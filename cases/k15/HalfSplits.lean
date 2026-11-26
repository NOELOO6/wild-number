import Std
namespace HalfSplits
set_option maxHeartbeats 0
def choose2 (a : Nat) := a*(a-1)/2

/-- On either half there are ten complementary pairs of triples. -/
structure Half where
  dark : Nat
  twice : Nat
  clear : Nat
deriving Inhabited
def halves := (List.range 21).flatMap fun a =>
  ((List.range (a/2+1)).filter (fun p => a ≤ 10+p)).map fun p => Half.mk a p (10+p-a)
structure Price where
  den : Int
  fixed : Int
  first : Int
  cross : Int
  square : Int
deriving Inhabited
def countPrices : List Price := [⟨746,50100,-2800,298,-545⟩,⟨84,4800,-230,47,-80⟩]
def splitPrices : List Price := [⟨819,819,-45,2,-9⟩,⟨630,630,-30,7,-10⟩,
    ⟨115,115,-7,0,-1⟩,⟨98,86,1,6,-8⟩]
def value (p : Price) (a b : Half) : Int :=
  let n : Int := (a.twice+b.twice : Nat)
  p.fixed+p.first*(a.dark+b.dark : Nat)+p.cross*((a.dark*b.dark : Nat)-20*n)
    +p.square*((choose2 a.dark+choose2 b.dark : Nat)-15*n)
def localCheck (split : Bool) (p : Price) := halves.all fun a => halves.all fun b =>
  let hits := a.clear*b.clear
  let reward := if split then min 1 hits else hits
  decide (value p a b ≤ p.den*(reward : Int))
theorem six_tables : countPrices.all (localCheck false) = true ∧
    splitPrices.all (localCheck true) = true := by native_decide

/-- Bounds on the sum of binomial(vertex degree,2) after deleting repeated triples. -/
def mostLostSquares (h : Nat) := ((List.range (h+1)).map fun z =>
  z*z + min z (h+9-z)*(3*h-z)).foldl max 0
def degreeLimit (m : Nat) : Nat :=
  let h := 75-m
  min ((51*m+243)/2) ((4068+mostLostSquares h-105*h)/2)
def summed (p : Price) (m : Nat) : Int :=
  462*p.fixed+84*(m : Int)*p.first
    +p.square*(21*(degreeLimit m : Int)-14*(choose2 m : Int))
theorem totals : (List.range' 40 36).all (fun m =>
    countPrices.any (fun p => decide (5470*p.den ≤ summed p m)) &&
    splitPrices.any (fun p => decide (107*p.den < summed p m))) = true := by native_decide
theorem small : (List.range 40).all (fun m =>
    1824 ≤ 15400-280*m && 108 ≤ 462-(84*m)/10) = true := by decide
theorem conclusions (layouts usable marked : Nat) (a : 5470 ≤ 3*layouts)
    (b : 107 < usable) (c : marked ≤ 96) : 1824 ≤ layouts ∧ 12 ≤ usable-marked := by omega
#print axioms six_tables
#print axioms totals
end HalfSplits
