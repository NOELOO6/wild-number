import Std
namespace K17
set_option maxRecDepth 200000

abbrev Matching := Array Nat
def points := Array.range 18
@[inline] def bit (v : Nat) := 1 <<< v
def root : Nat := 17
def ordinary := bit root - 1
def full := bit 18 - 1
@[inline] def withoutLow (m : Nat) := m &&& (m-1)
@[inline] def lowBit (m : Nat) := m ^^^ withoutLow m

structure Row where
  cycles : List Nat
  both : Nat
  prices : Array Int
  transfers : Array (Array Int)
  deriving Inhabited

def lines := ((include_str "prices.txt").trim.splitOn "\n").toArray.map fun l =>
  ((l.splitOn " ").filterMap String.toInt?).toArray

def data : Array Row := (Array.range 15).map fun i =>
  let start := i*17
  let header := lines[start]!
  { cycles := (header.toList.drop 1 |>.take header[0]!.toNat).map Int.toNat
    both := header.back!.toNat, prices := lines[start+1]!
    transfers := (Array.range 15).map fun j => lines[start+2+j]! }

def canonical (cycles : List Nat) : Matching × Matching := Id.run do
  let mut a := Array.replicate 18 0
  let mut b := Array.replicate 18 0
  let mut start := 0
  let point := fun k => if k == 0 then 17 else if k == 17 then 0 else k
  for n in cycles do
    for j in [:n/2] do
      let u := point (start+2*j)
      let v := point (start+2*j+1)
      let w := point (start+(2*j+2)%n)
      a := (a.set! u v).set! v u
      b := (b.set! v w).set! w v
    start := start+n
  return (a,b)

def chooseMasks (size count : Nat) : Array Nat := Id.run do
  let mut bins := (Array.replicate (count+1) (#[] : Array Nat)).set! 0 #[0]
  for v in [:size] do
    for step in [:count] do
      let d := count-step
      bins := bins.modify d (· ++ (bins[d-1]!.map (· ||| bit v)))
  return bins[count]!

/-- Four unordered triples on twelve fresh labels. The first unused label
    always belongs to the next triple. -/
def partitions : Array (Array Nat) := Id.run do
  let triples := chooseMasks 12 3
  let mut partials := #[(4095, (#[] : Array Nat))]
  for _ in [:3] do
    let mut next := #[]
    for (rest,gs) in partials do
      let first := lowBit rest
      for t in triples do
        if (t &&& first != 0) && (t &&& rest == t) then
          next := next.push (rest ^^^ t, gs.push t)
    partials := next
  return partials.map (fun (rest,gs) => gs.push rest)

/-- For each triple or six-set, all partitions which use it as one or
    two whole blocks. Partition identifiers are bits in a natural number. -/
def partIndex : Array Nat := Id.run do
  let mut ix := Array.replicate 4096 0
  for i in [:partitions.size] do
    let g := partitions[i]!
    let id := bit i
    for j in [:4] do
      ix := ix.modify g[j]! (· ||| id)
      for k in [:j] do ix := ix.modify (g[k]! ||| g[j]!) (· ||| id)
  return ix

def closed (m : Matching) : Array Bool := Id.run do
  let mut sides := #[0]
  for v in points do
    if v < m[v]! then
      let e := bit v ||| bit m[v]!
      sides := sides ++ sides.map (· ||| e)
  let mut table := Array.replicate (full+1) false
  for s in sides do table := table.set! s true
  return table

def deposit (left : Nat) : Array Nat := Id.run do
  let mut a := #[0]
  for v in [:17] do
    if left.testBit v then a := a ++ a.map (· ||| bit v)
  return a

def tripleMasks := chooseMasks 12 3
def sixMasks := chooseMasks 12 6
def allParts := bit partitions.size - 1
def failures (c : Array Bool) (big : Nat) (masks : Array Nat) : Nat := Id.run do
  if c[big ||| bit root]! then return allParts
  let mut ids := 0
  for t in tripleMasks do
    let s := masks[t]!
    if c[s ||| big]! || c[s ||| bit root]! then ids := ids ||| partIndex[t]!
  for t in sixMasks do
    if c[masks[t]!]! then ids := ids ||| partIndex[t]!
  return ids

def bitCounts := (Array.range 256).map fun n => ((List.range 8).filter n.testBit).length
def pop (s : Nat) : Nat := Id.run do
  let mut n := s
  let mut answer := 0
  for _ in [:s.log2/8+1] do
    answer := answer + bitCounts[n &&& 255]!
    n := n >>> 8
  return answer

structure Counts where
  one : Nat := 0
  both : Nat := 0
  freq : Array Nat := Array.replicate (full+1) 0
  deriving Inhabited

def countLayouts (a b : Matching) : Counts := Id.run do
  let ca := closed a
  let cb := closed b
  let mut freq := Array.replicate (full+1) 0
  let mut one := 0
  let mut both := 0
  for big in chooseMasks 17 5 do
    let masks := deposit (ordinary ^^^ big)
    let fa := failures ca big masks
    one := one + pop fa
    let mut hits := fa &&& failures cb big masks
    -- Scan small words so that locating bits does not repeatedly copy a long integer.
    for w in [:hits.log2/48+1] do
      let mut word := hits &&& (bit 48-1)
      hits := hits >>> 48
      for _ in [:48] do
        if word == 0 then break
        let id := 48*w + (lowBit word).log2
        word := withoutLow word
        let g := partitions[id]!
        both := both+1
        freq := freq.modify (big ||| bit root) (·+1)
        for j in [:4] do
          let s := masks[g[j]!]!
          freq := freq.modify (s ||| big) (·+1)
          freq := freq.modify (s ||| bit root) (·+1)
          for k in [:j] do freq := freq.modify (s ||| masks[g[k]!]!) (·+1)
  return ⟨one,both,freq⟩
end K17
