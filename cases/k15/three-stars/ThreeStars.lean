import VertexRedraw

namespace ThreeStars
open VertexRedraw EdgeWalk WildDeletion
abbrev K := Fin 7
abbrev Group := Fin 5
def codes : Array String := #["vvv","vv0","v00","v01","000","001","012"]
def inputs : Array String := #[include_str "vvv.txt",include_str "vv0.txt",include_str "v00.txt",
  include_str "v01.txt",include_str "000.txt",include_str "001.txt",include_str "012.txt"]

def rule (k : K) (box i j : Nat) : Nat :=
  let ch := (codes[k.val]!.toList)[box]!
  if ch == 'v' then j ^^^ (i ^^^ 3) else
    let s := ch.toNat - '0'.toNat
    let a := if s==0 then 1 else 0
    (j + (if i==3 then 0 else if i==s then 2 else if i==a then 1 else 3))%4

def required (k : K) (c : C) : R :=
  if c.val < 12 then (List.finRange 4).map (fun i =>
    (Fin.ofNat' 16 (4*(c.val/4)+rule k (c.val/4) i.val (c.val%4)),Fin.ofNat' 16 (12+i.val)))
  else (List.finRange 4).filterMap fun i =>
    let j := i.val ^^^ (3 ^^^ (c.val%4))
    if i.val < j then some (Fin.ofNat' 16 (12+i.val),Fin.ofNat' 16 (12+j)) else none
def unused (k : K) (c : C) := points.filter (fun v => !(required k c).any (fun e => e.1==v || e.2==v))
def candidates (k : K) (c : C) := (fills 16 (unused k c)).map (required k c ++ ·)

def mask (e : Edge 16) := 2^e.1.val ||| 2^e.2.val
def subsets : R → List Nat
  | [] => [0]
  | e::es => let tail := subsets es; tail ++ tail.map (· ||| mask e)
def full (m : R) := m.foldr (fun e v => v ||| mask e) 0
def regular (m : R) := full m == 65535 && m.all (fun e => decide (e.1 < e.2)) && decide m.Nodup

structure Layout where
  weight : Nat
  groups : List Nat
  deriving Inhabited
def wild (g : Layout) : E := g.groups.flatMap triple
def ordSides (g : Layout) := g.groups ++ Teams.unorderedPairs g.groups (· ||| ·)
def sides (g : Layout) := (ordSides g).flatMap (fun s => [s,s ||| 32768])
def recipes := inputs.map numbers
def recipe (k : K) := recipes[k.val]!
def costTables := recipes.map (fun r => r.head!.tail.toArray)
def costs (k : K) := costTables[k.val]!
def feeTables := recipes.map (fun r => r[1]!.tail.toArray)
def fees (k : K) := feeTables[k.val]!
def fee (k : K) (e : Edge 16) := if e.2.val < 12 then (fees k)[e.2.val*(e.2.val-1)/2+e.1.val]! else 0
def seeds (k : K) := ((recipe k).filter (fun r => r.head! == 2)).map List.tail
def moves (k : K) := ((recipe k).filter (fun r => r.head! == 3)).map (fun r => r.tail.toArray)
def moveMask (p : Array Nat) (s : Nat) := (List.range 15).foldl
  (fun a x => if s.testBit x then a ||| 2^p[x]! else a) 0
def layouts (k : K) := (seeds k).flatMap (fun r => (moves k).map fun p =>
  Layout.mk r.head! (r.tail.map (moveMask p)))

/-- One slot for each possible side of a cut. -/
def record (a : Array Nat) (g : Layout) :=
  (sides g).foldl (fun t s => t.modify s (· + g.weight)) a
def ledger (gs : List Layout) := gs.foldl record (Array.replicate 65536 0)
def lookup (a : Array Nat) (s : Nat) := a[s]?.getD 0
def spent (a : Array Nat) (m : R) := Teams.total (subsets m) (lookup a)
def entries := (List.finRange 12).flatMap fun j =>
  ((List.finRange 12).filter (· < j)).map fun i => ((Fin.ofNat' 16 i.val,Fin.ofNat' 16 j.val) : Edge 16)
def legal (g : Layout) := decide ((wild g).length=10 ∧ (wild g).Nodup ∧ ∀ e∈wild g,e.1<e.2)

def verify (k : K) :=
  let gs := layouts k
  let a := ledger gs
  colors.all (fun c => (candidates k c).all fun m =>
    regular m && decide (spent a m ≤ (costs k)[c.val]! + Teams.total m (fee k))) &&
  decide (Teams.total colors (fun c => (costs k)[c.val]!) + Teams.total entries (fee k) <
    Teams.total gs Layout.weight) && gs.all legal

end ThreeStars
