import EdgeWalk

namespace Wild21
open EdgeWalk

abbrev V := Fin 21
abbrev Edges := List (Edge 21)
def points := List.finRange 21
def dist (a b : V) := min (max a.val b.val - min a.val b.val)
  (21 - (max a.val b.val - min a.val b.val))

/-- From the least unpaired point, try each partner of an unused circular length. -/
def scan (test : Edges → Bool) : Nat → List V → List Nat → Edges → Bool
  | _, [], _, es => test es
  | 0, _::_, _, _ => false
  | fuel+1, a::rest, used, es => rest.all fun b =>
      dist a b ∈ used || scan test fuel (rest.erase b) (dist a b :: used) ((a,b)::es)

def point (i : Fin 7) (q : Nat) : V := ⟨(3*i.val+q)%21,Nat.mod_lt _ (by decide)⟩

/-- The triples are {3i, 3(i+a)+1, 3(i+b)+2}, for i modulo seven. -/
def layout (a b : Fin 7) : Edges := (List.finRange 7).flatMap fun i =>
  [(point i 0,point i (3*a.val+1)),(point i 0,point i (3*b.val+2))]

def shift (s : Edges) (c : V) : Edges := s.map fun (x,y) => (x+c,y+c)
def layouts : List Edges := (List.finRange 7).flatMap fun a =>
  (List.finRange 7).map (layout a)

def wins (w s : Edges) := ([0,1,2] : List V).all fun c => passes 0 (w ++ shift s c)
def acceptsStarter (s : Edges) := layouts.any fun w => wins w s

end Wild21
