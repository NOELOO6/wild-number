import SixBoundary

namespace SixBoundary
open VertexRedraw

def fours := (List.range 16).flatMap fun a => (List.range a).flatMap fun b =>
  (List.range b).flatMap fun c => (List.range c).map fun d => 2^a ||| 2^b ||| 2^c ||| 2^d
def starters := (FixedSix.triplesOn 0 15).map (· ||| 32768)
def outside (t : Nat) := fours.filter fun a => (t &&& a)==0

/-- If a matching maps the four starters to exactly the proposed four points,
every known partner must respect membership on the two sides. -/
def canMap (t a : Nat) (c : C) := points.all fun x =>
  !held c x || t.testBit x.val == a.testBit (ref c x).val

def allowed (t a : Nat) := bits (canMap t a) colors
def internalCount (t : Nat) := (colors.filter (canMap t t)).length
def table (t : Nat) := ((outside t).foldl (fun (arr : Array Nat) a =>
  arr.set! a (allowed t a)) (Array.replicate 65536 0)).set! t (allowed t t)

def possibleBox (t : Nat) :=
  decide (3 ≤ internalCount t) && (
    let choices := outside t
    let mask := table t
    choices.any fun a => choices.any fun b =>
      let d := 65535 ^^^ t ^^^ a ^^^ b
      a<b && (a &&& b)==0 && b<d &&
        (mask[t]! ||| mask[a]! ||| mask[b]! ||| mask[d]!) == 32767)

end SixBoundary
