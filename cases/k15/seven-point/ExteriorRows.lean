import BoundaryOptions
import StarGeometry

namespace ExteriorRows
open VertexRedraw ThreeStars EdgeWalk WildDeletion

def outside (x : V) := 6 ≤ x.val && x.val < 15
def lock (x y : V) := outside x && outside y
def key (x : V) := if outside x then x.val-5 else 0
def opts := colors.toArray.map fun c => (BoundaryOptions.possible lock c).toArray
def prices := ((numbers (include_str "exterior-prices.txt")).map List.toArray).toArray
def price (c : C) (t j : Nat) := prices[10*c.val+t]![j]!

def layouts := (FixedSix.endings.flatMap fun b => FixedSix.starts.map
  (fun a => Layout.mk 1 (a++b))).toArray
def groups := List.finRange 10
def ends := List.finRange 280
def index (j : Fin 280) (i : Fin 10) := 10*j.val+i.val
def layout (j : Fin 280) (i : Fin 10) := layouts[index j i]!
def bySide := (List.range 2800).foldl (fun (acc : Array Nat) k =>
  (sides layouts[k]!).foldl (fun a s => a.modify s (· ||| 2^k)) acc) (Array.replicate 65536 0)
def shadow (m : R) := (subsets m).foldl (fun n s => n ||| bySide[s]?.getD 0) 0
def root (m : R) := (m.findSome? (fun (x,y) =>
  if x.val==15 then some y else if y.val==15 then some x else none)).getD 15
def bits10 := (Array.range 1024).map fun v => (groups.filter (fun i => v.testBit i.val)).length
def digit (s : Nat) (j : Fin 280) := (s >>> (10*j.val)) % 1024
def count (s : Nat) (j : Fin 280) := bits10[digit s j]!
def assessed (c : C) (m : R) :=
  let s := shadow m
  let r := root m
  full m == 65535 && (m.contains (r,15) || m.contains (15,r)) &&
    ends.all (fun j => count s j ≤ price c (key r) j.val)

def allRows := colors.all (fun c => opts[c.val]!.all (assessed c))
def budget (t : C→Nat) (j : Fin 280) := Teams.total colors (fun c => price c (t c) j.val)
end ExteriorRows
