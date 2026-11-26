import FourStars
import SearchExample
namespace VertexRedraw
open EdgeWalk WildDeletion

def roundRobin := (List.range 15).map fun c => (Array.range 16).map fun x =>
  if x==15 then c else if x==c then 15 else (2*c+15-x)%15
def properRows (rs : List (Array Nat)) := rs.length==15 && rs.all (fun m => m.size==16 &&
  (Array.range 16).all (fun x => m[x]! < 16 && m[x]! != x && m[m[x]!]! == x)) &&
  (Array.range 16).all (fun x => (rs.map (fun m => m[x]!)).eraseDups.length == 15)

/-- Sizes of the components of the union of two color matchings. -/
def profile (a b : Array Nat) : List Nat := Id.run do
  let mut left := 65535
  let mut out := []
  for _ in [:4] do
    if left==0 then break
    let root := (left &&& (left ^^^ (left-1))).log2
    let mut x := root
    let mut n := 0
    for _ in [:8] do
      let y := a[x]!
      left := left ^^^ 2^x ^^^ 2^y
      n := n+2
      x := b[y]!
      if x==root then break
    out := n::out
  return out.mergeSort
def allowedProfile (p : List Nat) := [[16],[6,10],[4,6,6]].contains p
def pairsOK (rs : List (Array Nat)) (k : Nat) := (List.range 15).all fun c =>
  !k.testBit c || (List.range c).all fun d =>
    !k.testBit d || allowedProfile (profile rs[c]! rs[d]!)
def pairMasks := (Array.range 15).map fun c => (List.range c).foldl
  (fun z d => if allowedProfile (profile referenceRows[c]! referenceRows[d]!) then z ||| 2^d else z) 0
def clique (s : Nat) := (Array.range 15).all fun c =>
  !s.testBit c || (s &&& (2^c-1) &&& pairMasks[c]!) == (s &&& (2^c-1))
def size (s : Nat) := ((List.range 15).filter s.testBit).length
theorem different_families : properRows referenceRows.toList = true ∧
    properRows SearchExample.rows = true ∧ properRows roundRobin = true ∧
    pairsOK SearchExample.rows 32767 = true ∧ pairsOK roundRobin 32767 = true ∧
    ((List.range 32768).all fun s => !clique s || size s ≤ 6) = true ∧
    ((List.range 32768).any fun s => clique s && size s == 6) = true := by native_decide

def exampleColors := colors.map (fun c => actualEdges (partner c))
def trial (g : List Nat) := g.flatMap triple
def start : List Nat := [7,56,448,12800,19456]
def middle : List Nat := [13,50,448,12800,19456]
def finish : List Nat := [73,50,388,12800,19456]
def test (g : List Nat) := exampleColors.all fun m => passes 0 (trial g ++ m)
def swapBit (a b s : Nat) := if s.testBit a == s.testBit b then s else s ^^^ 2^a ^^^ 2^b
def swaps (g : List Nat) := (List.range 15).flatMap fun a => (List.range a).filterMap fun b =>
  if g.any (fun s => s.testBit a && s.testBit b) then none else some (g.map (swapBit a b))
theorem two_swaps : (colors.filter fun c => !passes 0 (trial start ++ actualEdges (partner c))) = [12] ∧
  (swaps start).length = 90 ∧ (swaps start).any test = false ∧
  middle ∈ swaps start ∧ finish ∈ swaps middle ∧
  (trial finish).length=10 ∧ (trial finish).Nodup ∧ test finish = true := by native_decide
theorem example_connected (c : C) : Connected (Adj (trial finish ++ actualEdges (partner c))) :=
  connected_of_passes 0 _ (List.all_eq_true.mp two_swaps.2.2.2.2.2.2.2 _ (List.mem_map.mpr
    ⟨c,(by decide : ∀ i : C, i ∈ colors) c,rfl⟩))
end VertexRedraw
