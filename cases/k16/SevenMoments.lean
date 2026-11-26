import Teams
/- Pointwise inequalities and the two-color intersection counts for every
   alternating cycle type on sixteen points, with a specified point. -/
namespace SevenMoments
open Teams
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def choose2 (k : Nat) := k*(k-1)/2
def good (x y : Nat) := if y == 0 && x ≤ 2 then 1 else 0
def anyGood (y : Nat) := if y == 0 then 1 else 0

theorem local_inequalities : (List.range 16).all (fun x =>
    (List.range 16).all (fun y =>
      !(2*y ≤ 6+x && 2*x ≤ 9+y && x+y ≤ 15) ||
      (15+2*x*y+6*choose2 y ≤ 15*good x y+17*y+5*choose2 x &&
       7+2*choose2 y ≤ 7*anyGood y+7*y))) = true := by decide

def seven := (List.range 65536).filter fun z =>
  z.testBit 0 && ((List.range 16).filter z.testBit).length == 7

def pairings : List Nat → Nat → Matching × Matching
  | [], _ => ([],[])
  | n::ns, first =>
    let js := List.range (n/2)
    let (m,u) := pairings ns (first+n)
    (js.map (fun j => pair (first+2*j) (first+2*j+1)) ++ m,
     js.map (fun j => pair (first+2*j+1) (first+(2*j+2)%n)) ++ u)

def types : List (List Nat) := [[16],[4,12],[12,4],[6,10],[10,6],[8,8],
  [4,4,8],[8,4,4],[4,6,6],[6,4,6],[4,4,4,4]]
def count (m : Matching) (z : Nat) := (m.filter (fun e => z &&& e == e)).length
def counts (q : List Nat) := Id.run do
  let (m,n) := pairings q 0
  let mut xx := 0
  let mut xy := 0
  let mut yy := 0
  let mut triples := 0
  for z in seven do
    let a := count m z
    let b := count n z
    if a == 3 then triples := triples+1
    if a == 0 && b == 0 then xx := xx+1
    if (a == 0 && b == 3) || (a == 3 && b == 0) then xy := xy+1
    if a == 3 && b == 3 then yy := yy+1
  return (triples,xx,xy,yy)

theorem pair_bounds : types.all (fun q =>
    let (t,xx,xy,yy) := counts q
    t == 245 && 7 ≤ yy && 5*xx+5 ≤ 2*xy+6*yy) = true := by native_decide

theorem final_count (qual goodCount totalY xx xy yy : Nat)
    (first : 15*5005+2*xy+6*yy ≤ 15*qual+17*totalY+5*xx)
    (second : 7*5005+2*yy ≤ 7*goodCount+7*totalY)
    (single : totalY = 15*245)
    (intersection : 105*5+5*xx ≤ 2*xy+6*yy)
    (overlap : 105*7 ≤ yy) : 875 ≤ qual ∧ 1540 ≤ goodCount := by omega

#print axioms local_inequalities
#print axioms pair_bounds
#print axioms final_count
end SevenMoments
