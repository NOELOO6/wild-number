import CyclicScan

namespace Wild21
open EdgeWalk

abbrev V := Fin 21
abbrev Edges := List (Edge 21)
def points := List.finRange 21
abbrev dist := @WildExact.Rotation.dist 21
abbrev scan := @WildExact.Rotation.scan 21

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
