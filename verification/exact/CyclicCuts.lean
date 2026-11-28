import CyclicScan

namespace WildExact.Rotation.CutTest
open EdgeWalk

variable {n : Nat}
abbrev V (n : Nat) := Fin (n+1)
abbrev Blocks (n : Nat) := List (List (V n))

def stars : List (V n) → List (Edge (n+1))
  | [] => []
  | x::xs => xs.map fun y => (x,y)

def drawing (bs : Blocks n) := bs.flatMap stars

/-- The vertex lists obtained by selecting whole blocks. -/
def unions : Blocks n → List (List (V n))
  | [] => [[]]
  | B::bs =>
    let rest := unions bs
    rest ++ rest.map (B++·)

def cuts (bs : Blocks n) : List (List (V n)) :=
  (unions bs).filter fun S => !S.isEmpty && !S.contains 0

/-- Bit i records membership of x in the ith side of the cut table. -/
def labels (x : V n) : List (List (V n)) → Nat
  | [] => 0
  | S::ss => 2*labels x ss + (if x∈S then 1 else 0)

def translated (ss : List (List (V n))) (c : V n) : Array Nat :=
  ((List.finRange (n+1)).map fun x => labels (x+c) ss).toArray

def crossed (bits : Array Nat) (es : List (Edge (n+1))) : Nat :=
  es.foldl (fun mask e => mask ||| (bits[e.1.val]! ^^^ bits[e.2.val]!)) 0

structure Table where
  full : Nat
  colors : List (Array Nat)

def table (bs : Blocks n) : Table :=
  let ss := cuts bs
  ⟨2^ss.length-1,(List.finRange (n+1)).map (translated ss)⟩

def pass (t : Table) (es : List (Edge (n+1))) : Bool :=
  t.colors.all fun bits => crossed bits es == t.full

end WildExact.Rotation.CutTest
