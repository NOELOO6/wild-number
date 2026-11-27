import GraphSearch
namespace WildExact.Four
open WildExact
abbrev V := Fin 13
abbrev EdgeTest := V → V → Bool
abbrev RootTest := V → Bool

def ordinary (r : Row 13) (a b : V) := decide (a≠b) && rowHas r (a.castSucc,b.castSucc)
def star (r : Row 13) (a : V) := rowHas r (a.castSucc,Fin.last 13)
def paired (e : EdgeTest) (a b c d : V) :=
  (e a b && e c d) || (e a c && e b d) || (e a d && e b c)

def marked (e : EdgeTest) (s : RootTest) (a b c d : V) :=
  (s a || s b || s c || s d) && (e a b || e a c || e a d || e b c || e b d || e c d)

def score (e : EdgeTest) (s : RootTest) (a b c d : V) : Int :=
  (if paired e a b c d then 2 else 0) + (if marked e s a b c d then 1 else 0)

end WildExact.Four

namespace WildExact.Nine
abbrev Family := Nat → Bool
def ids := List.range 84
def triples := (chooseK 3 (List.range 9)).map fun t => t.foldl (fun s i => s ||| (1 <<< i)) 0
def mask (i : Nat) : Nat := triples[i]?.getD 0
def hit (a b c : Nat) : Bool :=
  a < b && b < c && c < 84 && (mask a ||| mask b ||| mask c == 511)
def bits (s : Nat) := ((List.range 9).filter s.testBit).length
def limits : List (List Nat × Nat) := (ids,35) :: (List.range 512).flatMap fun s =>
  ([(1,1,23),(4,2,30),(7,3,33)] : List (Nat × Nat × Nat)).filterMap fun (k,t,b) =>
    if bits s = k then some (ids.filter (fun i => bits (mask i &&& s) ≥ t),b) else none

end WildExact.Nine
