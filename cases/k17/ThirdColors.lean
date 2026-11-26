import Groupings
namespace K17
set_option maxRecDepth 200000

@[inline] def edgeId (u v : Nat) := let hi := max u v; hi*(hi-1)/2 + min u v
/-- The base-four digits count non-root cycles of each possible length.
    There are at most three non-root cycles. -/
@[inline] def cycleDigit (n : Nat) := bit (2*(n/2-2))
def listKey (l : List Nat) : Nat := l.head! + 32*(l.tail.map cycleDigit).sum
def typeTable : Array Nat := Id.run do
  let mut a := Array.replicate 65536 15
  for i in [:15] do a := a.set! (listKey data[i]!.cycles) i
  return a

def matchingKey (a b : Matching) : Nat := Id.run do
  let mut rest := full
  let mut key := 0
  for i in [:4] do
    if rest == 0 then break
    let start := if i == 0 then root else (lowBit rest).log2
    let mut v := start
    let mut n := 0
    for _ in [:9] do
      let w := a[v]!
      rest := rest ^^^ bit v ^^^ bit w
      v := b[w]!
      n := n+2
      if v == start then break
    if i == 0 then key := n else key := key + 32*cycleDigit n
  return key

def matchingFrom (edges : List Nat) : Matching := Id.run do
  let mut m := Array.replicate 18 0
  for e in edges do
    let u := (lowBit e).log2
    let v := (withoutLow e).log2
    m := (m.set! u v).set! v u
  return m

structure Context where
  a : Matching
  b : Matching
  freq : Array Nat
  row : Row
  minTransfer : Int

@[inline] def addHits (f : Array Nat) (e : Nat) (xs : List Nat) (initial : Nat) :=
  xs.foldl (fun n s => n+f[e ||| s]!) initial

def affordable (ctx : Context) (cost : Nat) (fee : Int) (edges : List Nat) : Bool := Id.run do
  let need := 2*(cost : Int)-fee
  if need ≤ ctx.minTransfer then return true
  let m := matchingFrom edges
  let i := typeTable[matchingKey ctx.a m]!
  let j := typeTable[matchingKey ctx.b m]!
  return i < 15 && j < 15 && need ≤ ctx.row.transfers[i]![j]!

/-- Number of permitted completions. A single failed inequality instead returns
    none, which propagates all the way to the top. Each recursion pairs the
    first remaining vertex, so each legal third matching appears exactly once. -/
def verifyThird (ctx : Context) (depth left : Nat) (edges pairs triples : List Nat)
    (cost : Nat) (fee : Int) : Option Nat := Id.run do
  match depth with
  | 0 => return none
  | d+1 =>
    let u := (lowBit left).log2
    let remaining := withoutLow left
    let mut partners := remaining &&& (full ^^^ (bit ctx.a[u]! ||| bit ctx.b[u]!))
    let mut checked := 0
    for _ in [:17] do
      if partners == 0 then break
      let vBit := lowBit partners
      partners := withoutLow partners
      let e := bit u ||| vBit
      let c := addHits ctx.freq e triples (addHits ctx.freq e pairs (addHits ctx.freq e edges cost))
      let f := fee + ctx.row.prices[edgeId u vBit.log2]!
      if d == 0 then
        if !affordable ctx c f (e::edges) then return none
        checked := checked+1
      else
        let p := edges.foldl (fun acc s => (e ||| s)::acc) pairs
        let t := pairs.foldl (fun acc s => (e ||| s)::acc) triples
        match verifyThird ctx d (remaining ^^^ vBit) (e::edges) p t c f with
        | none => return none
        | some count => checked := checked+count
    return some checked

def expectedThird : Array Nat := #[11589764,11589764,11589469,11589469,11589180,
  11589180,11589180,11589177,11589177,11588896,11588888,11588888,11588883,
  11588883,11588884]

def checkCase (i : Nat) : Bool := Id.run do
  let row := data[i]!
  let (a,b) := canonical row.cycles
  let counts := countLayouts a b
  if counts.one != 8230880 || counts.both != row.both then return false
  let minTransfer := row.transfers.foldl (fun t r => r.foldl min t) 100000000
  let ctx : Context := ⟨a,b,counts.freq,row,minTransfer⟩
  return verifyThird ctx 9 full [] [] [] 0 0 == some expectedThird[i]!

end K17
