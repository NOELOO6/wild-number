import Example19
namespace WildPalette
abbrev V := Fin 20
abbrev C := Fin 19
abbrev G := Fin 7
abbrev Cut := Fin 64

/-- Complete the supplied nineteen-point matching in each color by adding
the edge from its missing point to the root. -/
def base (c : C) : Array Nat := Id.run do
  let mut a := Array.replicate 20 19
  for e in K19Exchange.color c do
    a := (a.set! e.1.val e.2.val).set! e.2.val e.1.val
  return a.set! 19 (a.findIdx (· == 19))
def mates := (List.finRange 19).toArray.map base
def partner (c : C) (v : V) : V := Fin.ofNat' 20 (mates[c.val]![v.val]!)

def labels : Array (Array Nat) := (((include_str "layouts.txt").trim.splitOn "\n").map fun l =>
  (l.toList.map (fun ch => ch.toNat-48)).toArray).toArray
def index := Id.run do
  let mut a := Array.replicate (2^19) 0
  for l in (include_str "palette-layouts.txt").trim.splitOn "\n" do
    if let [k,i] := (l.splitOn " ").map String.toNat! then a := a.set! k i
  return a
def group (r : Nat) (v : V) : G := Fin.ofNat' 7 (labels[r]![v.val]!)
def bit (r : Nat) (s : Cut) (v : V) := s.val.testBit (group r v).val

/-- A nontrivial even side of the partition. All odd sides are already
crossed by any perfect matching. -/
def size (r : Nat) (s : Cut) := ((List.finRange 20).filter (bit r s)).length
def tested (r : Nat) (s : Cut) := 0<size r s ∧ size r s<20 ∧ size r s%2=0
instance (r : Nat) (s : Cut) : Decidable (tested r s) := by unfold tested;infer_instance

def code (P : Finset C) := P.sum (fun c => 2^c.val)
def shared (r : Nat) (P : Finset C) : Prop := ∀ s : Cut,tested r s →
  ∃ x : V,∀ c∈P,bit r s x≠bit r s (partner c x)
def original (r : Nat) : Prop := ∀ s : Cut,tested r s → ∀ c : C,
  ∃ x : V,bit r s x≠bit r s (partner c x)
instance (r : Nat) (P : Finset C) : Decidable (shared r P) := by unfold shared;infer_instance
instance (r : Nat) : Decidable (original r) := by unfold original;infer_instance

def region (r : Nat) (j : G) : Finset V := Finset.univ.filter (fun x => group r x=j)
def regular (r : Nat) := region r 6={Fin.last 19} ∧
  ∀ j : Fin 6,(region r j.castSucc).card=(if j=0 then 4 else 3)
instance (r : Nat) : Decidable (regular r) := by unfold regular;infer_instance
end WildPalette
