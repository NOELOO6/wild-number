import GraphSearch
import Groupings

namespace WildExact.Seventeen
abbrev V := Fin 18
abbrev Table := Vector V 18

def entry (m : K17.Matching) (x : V) : V := Fin.ofNat' 18 (m[x.val]?.getD 0)
def canon (i : Fin 15) := K17.canonical K17.data[i.val]!.cycles
def first (x : V) : V :=
  let partners : Vector V 18 := ⟨#[16,17,3,2,5,4,7,6,9,8,11,10,13,12,15,14,0,1],rfl⟩
  partners.get x
def root : V := 17
def target : V := 2

/-- Read the partner from a list of disjoint edges. -/
def lookup : Row 17 → V → V
  | [],x => x
  | (a,b)::es,x => if x=a then b else if x=b then a else lookup es x

def live : List V := (List.finRange 18).filter (fun x => x != root && x != target)
def allow (a b : V) := a != b && first a != b

def visit {n} (allowed : Fin (n+1) → Fin (n+1) → Bool) (test : Row n → Bool) :
    Nat → List (Fin (n+1)) → Row n → Bool
  | _,[],acc => test acc
  | 0,_::_,_ => true
  | k+1,x::xs,acc => xs.all fun y => !allowed x y || visit allowed test k (xs.filter (· != y)) ((x,y)::acc)

def idTable : Table := Vector.ofFn id
def refA : Table := Vector.ofFn first
def refB : Vector Table 15 := Vector.ofFn fun i => Vector.ofFn (entry (canon i).2)
def typeIds := (List.finRange 15).map fun i => (K17.data[i.val]!.cycles,i)
def display (v : V) : V := if v=0 then root else if v=root then 0 else v

/-- Put the root cycle first, then the other alternating cycles in increasing length. -/
def orderedCycles (m : Table) : List (List V) := Id.run do
  let mut unseen : Nat := (1 <<< 18)-1
  let mut cycles : List (List V) := []
  for i in [:4] do
    if unseen=0 then break
    let v : V := if i=0 then root else Fin.ofNat' 18 ((unseen ^^^ (unseen &&& (unseen-1))).log2)
    let mut u := v
    let mut cycle : List V := []
    for _ in [:9] do
      let w := refA.get u
      cycle := w :: u :: cycle
      unseen := unseen ^^^ (1 <<< u.val) ^^^ (1 <<< w.val)
      u := m.get w
      if u=v then break
    cycles := cycle.reverse :: cycles
  match cycles.reverse with
  | [] => return []
  | h::tail => return h :: tail.mergeSort (fun a b => a.length ≤ b.length)

structure Witness where
  kind : Fin 15
  perm : Table
  inverse : Table

def witness (m : Table) : Witness := Id.run do
  let cycles := orderedCycles m
  let sizes := cycles.map List.length
  let i := ((typeIds.find? (fun p => p.1==sizes)).map Prod.snd).getD 0
  let order := cycles.flatten.toArray
  let p := Vector.ofFn fun (v : V) => order[(display v).val]?.getD root
  let q := (List.finRange 18).foldl (fun q v => q.set (p.get v).val v) idTable
  return ⟨i,p,q⟩

def validates (m : Table) (w : Witness) : Bool :=
  w.perm.get root == root && (List.finRange 18).all fun v =>
    w.inverse.get (w.perm.get v) == v && w.perm.get (w.inverse.get v) == v &&
    w.perm.get (refA.get v) == refA.get (w.perm.get v) &&
    w.perm.get ((refB.get w.kind).get v) == m.get (w.perm.get v)

def checkPair (r : Row 17) := let m := Vector.ofFn (lookup r); validates m (witness m)

def allSecond := visit allow checkPair 16 live [(root,target)]
end WildExact.Seventeen
