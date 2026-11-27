import PairData

namespace WildExact.Seventeen
abbrev Big := Fin 6188
abbrev Small := Fin 15400
abbrev Slot := Fin 14
abbrev Block := Fin 6
abbrev Layout := Big × Small

def bigMasks := K17.chooseMasks 17 5
def bigMask (b : Big) := bigMasks[b.val]?.getD 0
def smallMasks (p : Small) := K17.partitions[p.val]?.getD #[]
def flipNumber (k x : Nat) := if x=k then k+1 else if x=k+1 then k else x
def flipMask (k s : Nat) := if s.testBit k == s.testBit (k+1) then s else s ^^^ (3 <<< k)

def bigIndex := (Array.range bigMasks.size).foldl (fun a i => a.setIfInBounds bigMasks[i]! i)
  (Array.replicate (1 <<< 17) 0)

def bigStep (k : Fin 16) (b : Big) : Big := Fin.ofNat' 6188 (bigIndex[flipMask k.val (bigMask b)]?.getD 0)

def slots := Vector.ofFn fun b : Big => Vector.ofFn fun x : V =>
  if x.val=17 then (13 : Slot) else if (bigMask b).testBit x.val then (12 : Slot) else
    Fin.ofNat' 14 (((List.range x.val).filter (fun j => !(bigMask b).testBit j)).length)
def slot (b : Big) (x : V) := (slots.get b).get x
def branch (k : Fin 16) (b : Big) : Fin 12 :=
  if !(bigMask b).testBit k.val && !(bigMask b).testBit (k.val+1) then Fin.ofNat' 12 (slot b (Fin.ofNat' 18 k.val)).val else 11
def flipV (k : Fin 16) (x : V) : V := Fin.ofNat' 18 (flipNumber k.val x.val)
def flipSlot (k : Fin 12) (s : Slot) : Slot := if k.val<11 then Fin.ofNat' 14 (flipNumber k.val s.val) else s

def partKey (ts : List Nat) := (ts.mergeSort (·≤·)).foldl (fun a x => (a <<< 12) ||| x) 0
def partIndexMap : Std.HashMap Nat Nat := (Array.range K17.partitions.size).foldl
  (fun m i => m.insert (partKey K17.partitions[i]!.toList) i) {}
def smallSteps := Vector.ofFn fun k : Fin 12 => Vector.ofFn fun p : Small =>
  if k.val=11 then p else Fin.ofNat' 15400 (partIndexMap.getD (partKey ((smallMasks p).toList.map (flipMask k.val))) 0)
def smallStep (k : Fin 12) (p : Small) := (smallSteps.get k).get p
def tags := Vector.ofFn fun p : Small => Vector.ofFn fun s : Slot =>
  if s.val=13 then (0 : Block) else if s.val=12 then 1 else
    Fin.ofNat' 6 (2+(smallMasks p).findIdx (fun t => t.testBit s.val))
def tag (p : Small) (s : Slot) := (tags.get p).get s
def owner (l : Layout) (x : V) := tag l.2 (slot l.1 x)
def sameBlock (l : Layout) (x y : V) := owner l x == owner l y

def nextLayout (k : Fin 16) (l : Layout) : Layout :=
  (bigStep k l.1,smallStep (branch k l.1) l.2)

end WildExact.Seventeen
