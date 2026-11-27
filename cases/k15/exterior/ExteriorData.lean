import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
namespace WildExterior
open Finset

abbrev Port := Fin 9
abbrev Pairs := Finset (Finset Port)
def used (p : Pairs) := p.biUnion id
def star (u : Option Port) : Finset Port := u.toList.toFinset
def rootTriples (p : Pairs) (u : Option Port) : Finset (Finset Port) :=
  match u with
  | none => ∅
  | some x => p.image (insert x)
def blocked (p : Pairs) (u : Option Port) :=
  if p.card=3 then insert (used p)ᶜ (rootTriples p u) else rootTriples p u

def pairs9 := (univ : Finset Port).powersetCard 2
def rows := (pairs9.powersetCard 1∪pairs9.powersetCard 2∪pairs9.powersetCard 3).filter
  fun p => (used p).card=2*p.card

def admissible (p : Pairs) (u : Option Port) : Prop :=
  Disjoint (star u) (used p) ∧ (u=none → 2≤p.card)
instance (p : Pairs) (u : Option Port) : Decidable (admissible p u) := by unfold admissible;infer_instance

theorem row_mem (p : Pairs) (edges : ∀ e∈p,e.card=2) (lo : 1≤p.card) (hi : p.card≤3)
    (many : (used p).card=2*p.card) : p∈rows := by
  have sub : p⊆pairs9 := fun e h => mem_powersetCard.mpr ⟨subset_univ _,edges e h⟩
  unfold rows
  refine mem_filter.mpr ⟨?_,many⟩
  rcases (show p.card=1 ∨ p.card=2 ∨ p.card=3 by omega) with h|h|h
  · exact mem_union_left _ (mem_union_left _ (mem_powersetCard.mpr ⟨sub,h⟩))
  · exact mem_union_left _ (mem_union_right _ (mem_powersetCard.mpr ⟨sub,h⟩))
  · exact mem_union_right _ (mem_powersetCard.mpr ⟨sub,h⟩)

def degree (H : Finset (Finset Port)) (W : Finset Port) (t : Nat) :=
  (H.filter (fun T => t≤(T∩W).card)).card

/-- The complete count and the three subset tests from the nine-point
obstruction theorem. The four right sides sum over colors by counting
ordinary edges or partners of the fixed root. -/
def RowOK (p : Pairs) (u : Option Port) : Prop :=
  let B := blocked p u
  let tap := (star u).card
  2*B.card+6≤3*p.card+5*tap ∧
  (∀ x : Port,degree B {x} 1+(if x∈used p then 1 else 0)≤1+tap+2*(if x∈star u then 1 else 0)) ∧
  (∀ W∈(univ : Finset Port).powersetCard 4,degree B W 2+2≤p.card+2*tap) ∧
  (∀ W∈(univ : Finset Port).powersetCard 7,degree B W 3+2≤p.card+tap+((star u)∩W).card)
instance (p : Pairs) (u : Option Port) : Decidable (RowOK p u) := by unfold RowOK;infer_instance

end WildExterior
