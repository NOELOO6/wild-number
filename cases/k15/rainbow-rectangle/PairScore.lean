import Endgame
namespace PairScore
open Endgame
def pairs : List Pairing := [[(0, 10), (1, 6), (2, 13), (3, 11), (4, 7), (5, 15), (8, 12), (9, 14)],
  [(0, 7), (1, 3), (2, 4), (5, 13), (6, 10), (8, 15), (9, 12), (11, 14)],
  [(0, 11), (1, 15), (2, 8), (3, 14), (4, 10), (5, 9), (6, 12), (7, 13)],
  [(0, 1), (2, 15), (3, 9), (4, 6), (5, 8), (7, 10), (11, 13), (12, 14)],
  [(0, 3), (1, 8), (2, 6), (4, 11), (5, 7), (9, 15), (10, 14), (12, 13)],
  [(0, 14), (1, 10), (2, 5), (3, 8), (4, 9), (6, 13), (7, 15), (11, 12)],
  [(0, 6), (1, 2), (3, 12), (4, 8), (5, 10), (7, 9), (11, 15), (13, 14)],
  [(0, 15), (1, 5), (2, 9), (3, 13), (4, 12), (6, 7), (8, 14), (10, 11)],
  [(0, 13), (1, 9), (2, 12), (3, 5), (4, 15), (6, 14), (7, 11), (8, 10)],
  [(0, 12), (1, 4), (2, 11), (3, 7), (5, 14), (6, 15), (8, 13), (9, 10)],
  [(0, 9), (1, 14), (2, 10), (3, 4), (5, 11), (6, 8), (7, 12), (13, 15)],
  [(0, 2), (1, 11), (3, 15), (4, 14), (5, 12), (6, 9), (7, 8), (10, 13)],
  [(0, 5), (1, 12), (2, 3), (4, 13), (6, 11), (7, 14), (8, 9), (10, 15)],
  [(0, 4), (1, 7), (2, 14), (3, 10), (5, 6), (8, 11), (9, 13), (12, 15)],
  [(0, 8), (1, 13), (2, 7), (3, 6), (4, 5), (9, 11), (10, 12), (14, 15)]]
def colors := pairs.map edgeSet
def root := 1 <<< 15
def edge (x y : Nat) := (1 <<< x) ||| (1 <<< y)
def proper := (List.range 16).all (fun v =>
  colors.all (fun m => (m.filter (fun e => e.testBit v)).length == 1) &&
  (List.range 16).all (fun w => v==w || (colors.filter (fun m => m.contains (edge v w))).length == 1))

def triples15 := (List.range 15).flatMap fun z => (List.range z).flatMap fun y =>
  (List.range y).map fun x => edge x y ||| (1 <<< z)
def starts := ((List.range 13).map (fun d => 3 ||| (1 <<< (d+2)))).flatMap fun a =>
  (triples15.filter (fun b => (a &&& b)==0)).map fun b => (a,b)

/-- The seven-point test, evaluated on the actual edges of all fifteen colors. -/
def score (a b : Nat) : Option Nat := Id.run do
  let seven := root ||| a ||| b
  let mut total := 36
  for m in colors do
    let ins := m.filter (fun e => (e &&& seven)==e)
    if ins.length>2 then return none
    if let [p,q] := ins then
      let four := p ||| q
      if four==(root ||| a) || four==(root ||| b) then return none
      if (four &&& root)!=0 then total := total+1
      else if number (four &&& a)==2 then total := total+3
  return some total

def values := starts.filterMap fun (a,b) => score a b
def groups : List (List Nat) := [[0, 1, 3], [2, 7, 13], [4, 5, 6], [8, 9, 14], [10, 11, 12]]
def wild := groups.flatMap (fun g => [edge g[0]! g[1]!,edge g[1]! g[2]!])
def flood (edges : List Nat) : Nat → Nat → Nat
  | 0, seen => seen
  | k+1, seen => flood edges k (edges.foldl (fun t e => if (t &&& e)==0 then t else t ||| e) seen)
def connected (m : Teams.Matching) :=
  flood ((wild++m).filter (fun e => (e &&& root)==0)) 15 1 == 32767

theorem no_low_score : proper=true ∧ starts.length=2860 ∧ values.min?=some 40 := by native_decide

theorem pair_can_stay : wild.length=10 ∧ wild.Nodup ∧
    groups.any (fun g => g.contains 0 && g.contains 1)=true ∧ colors.all connected=true := by native_decide

#print axioms no_low_score
#print axioms pair_can_stay
end PairScore
