import Counting
namespace CountingSquares
open Counting
set_option maxRecDepth 300000
set_option maxHeartbeats 0

structure Part where
  n : Nat
  common : Nat
  intersectMask : Nat
  left : Nat
  right : Nat
deriving Inhabited

def part (e : List Nat) (s : Nat) : Part :=
  match allPresent e s with
  | [] => ⟨0,0,0,0,0⟩
  | [a] => ⟨1,0,0,a,0⟩
  | [a,b] => let q := a &&& b; ⟨2,pc q,q,a ^^^ q,b ^^^ q⟩
  | _ => ⟨3,0,0,0,0⟩
def tally (s t m : Nat) := 4*pc (s &&& m)+pc (t &&& m)
def flagKey (s t : Nat) (p : Part) :=
  let a := tally s t p.left
  let b := tally s t p.right
  let common := tally s t p.intersectMask
  let x := if p.n==1 then a else min a b
  let y := if p.n==1 then 0 else max a b
  (((p.n*4+p.common)*16+common)*16+x)*16+y
def typeMap (flags : Array Nat) := Id.run do
  let mut table := Array.replicate 49152 65535
  for (v,i) in (flags.toList.drop 2).zipIdx do table := table.set! v i
  return table
def selections (n m : Nat) := Id.run do
  let left := (List.range 4096).filter (fun s => pc s==n)
  let right := (List.range 4096).filter (fun t => pc t==m)
  let mut choices := #[]
  for s in left do
    for t in right do if (s &&& t)==0 then choices := choices.push (s,t)
  return choices
def diagrams (e : List Nat) :=
  ((List.range (bit e.length)).filter (fun m => pc m≤2)).toArray
def joins (e : List Nat) (ms : Array Nat) := Id.run do
  let mut pairs := #[]
  for i in [:ms.size] do
    for j in [:ms.size] do
      if (ms[i]! ||| ms[j]!) + 1 == bit e.length then pairs := pairs.push (i,j)
  return pairs

/-- For each placement of the two point sets and each ordered pair of
    flags covering the fixed union, count its two flag indices. -/
def gramRow (choices : Array (Nat × Nat)) (table : Array Nat) (nf : Nat)
    (e : List Nat) : Array Nat := Id.run do
  let subsets := diagrams e
  let ps := subsets.map (part e)
  let pairs := joins e subsets
  let mut gram := Array.replicate (nf*nf) 0
  let mut ids := Array.replicate ps.size 0
  for (s,t) in choices do
    for i in [:ps.size] do ids := ids.set! i table[flagKey s t ps[i]!]!
    for (i,j) in pairs do
      let index := nf*ids[i]!+ids[j]!
      if index ≥ gram.size then return #[]
      gram := gram.modify index (· + 1)
  return gram

def checkType (k : Nat) : Bool := Id.run do
  let flags := flagTypes[k]!
  let nf := flags.size-2
  let table := typeMap flags
  let choices := selections flags[0]! flags[1]!
  let rows := squares.toList.zipIdx.filter (fun (z,_) => z[0]!.toNat==k)
  for g in [:graphs.size] do
    let gram := gramRow choices table nf graphs[g]!
    if gram.size != nf*nf then return false
    let terms := (gram.toList.zipIdx.filter (fun (v,_) => v>0)).map
      (fun (v,i) => (v,i/nf+1,i%nf+1))
    for (z,i) in rows do
      if z.size != nf+1 then return false
      let coeff := terms.foldl (fun (a : Int) (v,x,y) => a+(v:Int)*z[x]!*z[y]!) 0
      if coeff*(multiplicities[g]! : Int) != expansions[i]![g]! then return false
  return true

theorem exact_squares : squares.size = expansions.size ∧
    expansions.all (fun row => row.size==83) = true ∧
    squares.all (fun row => decide (0≤row[0]! ∧ row[0]!.toNat<flagTypes.size)) = true ∧
    (List.range flagTypes.size).all checkType = true := by native_decide
theorem two_survivors (candidates spoiled : Nat) (hc : 2300 < candidates)
    (hb : spoiled ≤ 2299) : 2 ≤ candidates-spoiled := by omega
#print axioms exact_squares
end CountingSquares
