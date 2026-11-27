import LayoutData

namespace WildExact.Seventeen

def namedPairs := (List.finRange 6).flatMap fun i => ((List.finRange 6).filter (i < ·)).map (i,·)

def encode {n} (p : Fin n → Bool) : Nat :=
  (List.finRange n).foldl (fun s x => if p x then s ||| (1 <<< x.val) else s) 0

def localMask (p : Small) (i j : Block) := encode (fun s => tag p s == i || tag p s == j)
def cutLists := Vector.ofFn fun p : Small => namedPairs.map fun z => localMask p z.1 z.2
def localCuts (p : Small) := cutLists.get p

def allKeys : List Nat :=
  [12288] ++ K17.tripleMasks.toList.map (fun x => x ||| 4096) ++
  K17.tripleMasks.toList.map (fun x => x ||| 8192) ++ K17.sixMasks.toList

def partFlags (key : Nat) := if key=12288 then K17.allParts else K17.partIndex[key &&& 4095]?.getD 0
def sliceMap := Vector.ofFn fun b : Big => Vector.ofFn fun j : Fin 4 => Vector.ofFn fun t : Fin 16 =>
  encode (fun v : V => (t.val <<< (4*j.val)).testBit (slot b v).val)
def slice (b : Big) (j : Fin 4) (t : Nat) :=
  (((sliceMap.get b).get j).get (Fin.ofNat' 16 ((t >>> (4*j.val)) &&& 15)))
def embed (b : Big) (s : Nat) := slice b 0 s ||| slice b 1 s ||| slice b 2 s ||| slice b 3 s

def closedOn (f : V → V) (s : Nat) :=
  (List.finRange 18).all fun v => s.testBit v.val == s.testBit (f v).val

def closedTable (f : V → V) : Vector Bool 262144 := Vector.ofFn fun s => closedOn f s.val
def fastClosed (table : Vector Bool 262144) (s : Nat) :=
  table.get (Fin.ofNat' 262144 s)

/-- Bits for all local partitions cut off by at least one of the fifteen sides. -/
def badBits (t : Vector Bool 262144) (b : Big) :=
  allKeys.foldl (fun s k => if fastClosed t (embed b k) then s ||| partFlags k else s) 0

def bucket (i : Fin 280) : List Small := (List.finRange 55).map fun j => ⟨55*i.val+j.val,by have := i.isLt; have := j.isLt; omega⟩
def selected (s : Nat) := (List.finRange 280).flatMap fun i =>
  let word := (s >>> (55*i.val)) &&& ((1 <<< 55)-1)
  if word=0 then [] else (bucket i).filter (fun p => word.testBit (p.val%55))

def together (a b : Vector Bool 262144) (i : Big) := selected (badBits a i &&& badBits b i)
def oneCount (a : Vector Bool 262144) := ((List.finRange 6188).map (fun i => (selected (badBits a i)).length)).sum

structure Tally where
  both : Nat
  frequency : Array Nat

def blank : Tally := ⟨0,Array.replicate 262144 0⟩
def addCut (table : Array Nat) (s : Nat) := table.modify s (·+1)
def reportLocal (i : Big) (t : Array Nat) (p : Small) :=
  (localCuts p).foldl (fun z k => addCut z (embed i k)) t
def reportBig (a b : Vector Bool 262144) (t : Tally) (i : Big) : Tally :=
  let hits := together a b i
  ⟨t.both+hits.length,hits.foldl (reportLocal i) t.frequency⟩
def stats (f g : V → V) :=
  (List.finRange 6188).foldl (reportBig (closedTable f) (closedTable g)) blank

end WildExact.Seventeen
