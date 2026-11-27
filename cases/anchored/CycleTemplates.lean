import PairTable
namespace WildAnchor
open Finset WildExact

private def exchange (m a b : Nat) : Equiv.Perm (Fin m) :=
  if ha : a<m then if hb : b<m then Equiv.swap ⟨a,ha⟩ ⟨b,hb⟩ else Equiv.refl _ else Equiv.refl _

private def chunks (m offset : Nat) : List Nat → Equiv.Perm (Fin m)
  | [] => Equiv.refl _
  | l::ls =>
    let ring := (List.range (l-1)).foldl (fun p j => p.trans (exchange m offset (offset+j+1))) (Equiv.refl _)
    ring.trans (chunks m (offset+l) ls)

def cyclePerm (m : Nat) (cs : List Nat) := chunks m 0 cs

def bill (m : Nat) (table : Nat × Nat → Nat) (cs : List Nat) :=
  ∑ b : Mask m, table (key (row (cyclePerm m cs) (bits b)))

end WildAnchor
