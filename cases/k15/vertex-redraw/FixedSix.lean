import Repair
namespace FixedSix
open VertexRedraw EdgeWalk WildDeletion
def rows := (numbers (include_str "six-point-search.txt")).map List.toArray
def ordinary := rows.map fun m => actualEdges (fun v => Fin.ofNat' 16 m[v.val]!)
def triplesOn (first size : Nat) :=
  (List.range size).flatMap fun a => (List.range a).flatMap fun b =>
    (List.range b).map fun c => 2^(first+a) ||| 2^(first+b) ||| 2^(first+c)
def starts := (triplesOn 0 6).filterMap fun a =>
  let b := 63 ^^^ a
  if a<b then some [a,b] else none
def endings := (triplesOn 6 9).flatMap fun u => (triplesOn 6 9).filterMap fun v =>
  let w := 32704 ^^^ u ^^^ v
  if u<v && (u &&& v)==0 && v<w then some [u,v,w] else none
def all := starts.flatMap (fun s => endings.map (s++·))
def succeeds (g : List Nat) := ordinary.all (fun m => passes 0 (trial g++m))
def certifiedFailure (g : List Nat) := (g++Teams.unorderedPairs g (· ||| ·)).any fun s =>
  ordinary.any fun m => isolates s (trial g++m)
def counts := starts.map fun s => (endings.filter (fun u => succeeds (s++u))).length
def seven := 32831
def sparse := rows.all fun m => ((List.range 16).filter fun x =>
  seven.testBit x && seven.testBit m[x]! && x<m[x]!).length ≤ 2

theorem fixed_six_count : properRows rows=true ∧ sparse=true ∧ starts.length=10 ∧
    endings.length=280 ∧ all.length=2800 ∧ (all.filter succeeds).length=19 ∧
    (all.filter certifiedFailure).length=2781 ∧ counts.mergeSort=[0,0,0,0,0,0,2,2,7,8] := by native_decide
#print axioms fixed_six_count
end FixedSix
