import CutData
import PairTypes
namespace WildExact.Seventeen

def edgeId (a b : V) := let hi := max a.val b.val; hi*(hi-1)/2+min a.val b.val
def price (i : Fin 15) (a b : V) := K17.data[i.val]!.prices[edgeId a b]?.getD 0
def transfer (i j k : Fin 15) := (K17.data[i.val]!.transfers[j.val]?.getD #[])[k.val]?.getD 0
def minTransfer (i : Fin 15) := (List.finRange 15).foldl (fun low j =>
  (List.finRange 15).foldl (fun v k => min v (transfer i j k)) low) 100000000

def edgeMask (e : V × V) := (1 <<< e.1.val) ||| (1 <<< e.2.val)
def unions : Nat → List Nat → List Nat
  | 0,_ => [0]
  | _+1,[] => []
  | k+1,e::ms => (unions k ms).map (e ||| ·) ++ unions (k+1) ms

def valueAt (freq : Array Nat) (s : Nat) := freq[s]?.getD 0
def countMore (freq : Array Nat) (m : Nat) (xs : List Nat) (base : Nat) :=
  xs.foldl (fun a s => a+valueAt freq (m ||| s)) base

structure Prefix where
  row : Row 17
  singles : List Nat
  pairs : List Nat
  triples : List Nat
  cost : Nat
  charge : Int

def start : Prefix := ⟨[],[],[],[],0,0⟩
def extend (i : Fin 15) (freq : Array Nat) (e : V × V) (p : Prefix) : Prefix :=
  let m := edgeMask e
  let cost := countMore freq m p.triples (countMore freq m p.pairs (countMore freq m p.singles p.cost))
  ⟨e::p.row,m::p.singles,p.singles.map (m ||| ·) ++ p.pairs,p.pairs.map (m ||| ·) ++ p.triples,
    cost,p.charge+price i e.1 e.2⟩

def permits (i : Fin 15) (lo : Int) (p : Prefix) :=
  let need := 2*(p.cost : Int)-p.charge
  if need ≤ lo then true else
    let m := Vector.ofFn (lookup p.row)
    let b := refB.get i
    let j := typeOf refA.get m.get
    let k := typeOf b.get m.get
    decide (need ≤ transfer i j k)

def allowedThird (i : Fin 15) (a b : V) := refA.get a != b && (refB.get i).get a != b

/-- Each branch follows one edge of a prospective third matching. The prefix
reuses the costs for matching-edge subsets already examined on that branch. -/
def inspect (i : Fin 15) (freq : Array Nat) (lo : Int) :
    Nat → List V → Prefix → Bool
  | _,[],p => permits i lo p
  | 0,_::_,_ => true
  | k+1,x::xs,p => xs.all fun y => !allowedThird i x y ||
      inspect i freq lo k (xs.filter (· != y)) (extend i freq (x,y) p)

def certified (i : Fin 15) :=
  let data := stats refA.get (refB.get i).get
  data.both == K17.data[i.val]!.both && inspect i data.frequency (minTransfer i) 9 (List.finRange 18) start

end WildExact.Seventeen
