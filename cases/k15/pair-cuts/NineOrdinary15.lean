import BlockCatalogue
import Endgame

namespace NineOrdinary15
open Endgame
set_option maxHeartbeats 0
set_option maxRecDepth 200000

/-- The constant entry of each price is charged once per color. -/
def rules : List Rule := [
  ⟨0,#[1,1,1,1],37,2,#[0,-1,-1,0,0,5,-1,0,0,5,0,0,0,0,0,4]⟩,
  ⟨3,#[3,2,0,0],82,2,#[0,-2,-2,0,0,10,-3,-2,0,10,-2,0,0,0,0,12]⟩,
  ⟨1,#[0,1,0,0],25,1,#[0,0,0,1,0,3,0,1,0,1,3,0,0,0,0,0]⟩,
  ⟨1,#[1,0,0,0],31,2,#[0,0,-1,0,0,4,-1,-2,0,4,-1,0,0,0,0,4]⟩,
  ⟨3,#[0,1,2,2],51,1,#[0,2,0,1,0,5,0,1,0,3,1,0,0,0,0,0]⟩,
  ⟨4,#[0,0,1,1],29,2,#[0,1,0,1,0,5,0,1,0,4,1,0,0,0,0,0]⟩,
  ⟨4,#[2,0,3,0],98,4,#[0,-1,-1,6,0,28,-1,5,0,28,5,0,6,0,0,4]⟩]

def marks (m : Teams.Matching) := triples.filter (fun t =>
  closedAt m (outside ^^^ t) || closedAt m (ordinaryA ||| t) || closedAt m (ordinaryB ||| t))

def priceTest (r : Rule) (p : Pairing) :=
  let m := edgeSet p
  (m.filter (fun e => (e &&& zone) == e)).length > 2 ||
    decide (((r.denominator * weighted r (((1 <<< r.size)-1) <<< 7) (marks m) : Nat) : Int)
      ≤ (p.map (fun (x,y) => priceFor r x y)).sum + r.price[15]!)

def priceTotal (r : Rule) :=
  (edges.map (fun (x,y) => priceFor r x y)).sum + 15*r.price[15]!

theorem matching_bounds : rules.all (fun r =>
    (rows r.size).all (priceTest r) &&
    decide (priceTotal r < ((r.denominator*(r.limit+1) : Nat) : Int))) = true := by
  native_decide

/-- A further prescribed outside partition adds three triples whose
intersection sizes with the chosen subset sum to its size. -/
def extra (r : Rule) := ((List.range 4).flatMap (fun a =>
    (List.range 4).flatMap (fun b => ((List.range 4).filter (fun c => a+b+c=r.size)).map
      (fun c => r.w[a]!+r.w[b]!+r.w[c]!)))).foldl max 0

def excludes (r : Rule) (b : Array Nat) := (List.range 512).any fun s =>
  number s == r.size &&
  decide (r.limit+extra r < (b.toList.map (fun t => r.w[number (t &&& s)]!)).sum)

def small := BlockCatalogue.catalogue.filter (fun b => b.size ≤ 40)

theorem no_small_blocker : small.size = 89 ∧
    small.all (fun b => rules.any (fun r => excludes r b)) = true := by native_decide

#print axioms matching_bounds
#print axioms no_small_blocker
end NineOrdinary15
