import CyclicPrune
import CyclicCuts

namespace Wild27
open EdgeWalk WildExact.Rotation

abbrev V := Fin 27
abbrev Edges := List (Edge 27)
abbrev Groups := CutTest.Blocks 26

def point (i : Fin 9) (d : Nat) : V := ⟨(3*i.val+d)%27,Nat.mod_lt _ (by decide)⟩
def regular (a b : Fin 9) : Groups :=
  (List.finRange 9).map fun i => [point i 0,point i (3*a.val+1),point i (3*b.val+2)]

/-- These five additional orders cover the normalized starters for which
all 81 translation-invariant arrangements fail. -/
def extras : List (List V) := [
  [24,6,18,11,8,21,26,12,2,4,0,22,17,15,7,14,10,23,13,16,5,20,19,9,1,3,25],
  [12,24,10,1,19,8,23,11,20,21,25,14,22,17,4,6,7,15,2,26,0,3,9,18,5,16,13],
  [2,5,13,19,0,16,14,23,3,7,18,4,10,20,26,22,1,15,11,12,21,25,8,17,24,9,6],
  [16,14,23,20,13,5,3,4,19,21,12,26,1,18,7,11,9,6,25,24,22,0,15,8,17,2,10],
  [18,11,4,16,6,14,3,5,8,17,23,13,0,25,19,22,9,2,24,7,1,21,12,20,26,15,10]]

structure Candidate where
  groups : Groups
  periodic : Bool

def layouts : List Candidate :=
  ((List.finRange 9).flatMap fun a => (List.finRange 9).map fun b => ⟨regular a b,true⟩) ++
    extras.map fun order => ⟨(List.range 9).map (fun i => (order.drop (3*i)).take 3),false⟩

def reps (w : Candidate) : List V := if w.periodic then [0,1,2] else List.finRange 27
def rep (w : Candidate) (z : V) : V :=
  if w.periodic then ⟨z.val%3,by have := Nat.mod_lt z.val (by decide : 0<3); omega⟩ else z

def entry (w : Candidate) : CutTest.Table :=
  let ss := CutTest.cuts w.groups
  ⟨2^ss.length-1,(reps w).map (CutTest.translated ss)⟩

def tables := layouts.map entry
def acceptsStarter (s : Edges) := tables.any fun t => CutTest.pass t s

def limits := unitLimits 26
def allowed (t x y : V) := allowedUnitEdge limits t x y

def check (t : V) := scanAllowed (allowed t) acceptsStarter 13 (List.finRange 27).tail [] []
end Wild27
