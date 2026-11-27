import RootRegions
namespace WildSieve
open Finset

def sixWeight (h j : Nat) := h.choose 3*(10*ways (j-2))
def sixOverlap (h j : Nat) := h.choose 3*(h-3).choose 3*(100*ways (j-4))
def rootWeight (h j : Nat) := h*ways (j-1)
def rootOverlap (h j : Nat) := h.choose 3*((h-3)*(10*ways (j-3)))

def saving (rooted : Bool) (h j : Nat) :=
  (2*sixWeight h j + (if rooted then 2*rootWeight h j else 0) -
    (sixOverlap h j + (if rooted then 2*rootOverlap h j else 0)))/2

variable {I V : Type} [DecidableEq I] [DecidableEq V] [Fintype V]

theorem save_even (X : Finset V) (P : Finset I) (edge : I → Finset V)
    (sz : ∀ i∈P,(edge i).card=2) (apart : (P : Set I).PairwiseDisjoint edge)
    (inside : points edge P⊆X) (j : Nat) (len : X.card=3*j) (lo : 4≤j)
    (M : Finset (Layout X)) (lost : sixHits X P edge⊆Mᶜ) :
    M.card≤ways j-saving false P.card j := by
  classical
  have a := six_coverage X P edge sz apart inside j len lo
  have b := card_le_card lost
  have c := card_le_univ M
  rw [card_compl,card_layout j X len] at b
  rw [card_layout j X len] at c
  change 2*sixWeight P.card j≤2*(sixHits X P edge).card+sixOverlap P.card j at a
  simp only [saving,Bool.false_eq_true,if_false,add_zero]
  omega

theorem save_odd (X : Finset V) (P : Finset I) (edge : I → Finset V) (z : V)
    (sz : ∀ i∈P,(edge i).card=2) (apart : (P : Set I).PairwiseDisjoint edge)
    (inside : points edge P⊆X) (zx : z∈X) (free : z∉points edge P)
    (j : Nat) (len : X.card=3*j) (lo : 4≤j) (M : Finset (Layout X))
    (lost6 : sixHits X P edge⊆Mᶜ) (lost3 : rootHits X P edge z⊆Mᶜ) :
    M.card≤ways j-saving true P.card j := by
  classical
  let A := sixHits X P edge
  let B := rootHits X P edge z
  have a := six_coverage X P edge sz apart inside j len lo
  have b := root_coverage X P edge z sz apart inside zx free j len (by omega)
  have d := cross_coverage X P edge z sz apart inside zx free j len (by omega)
  have all := card_le_card (union_subset lost6 lost3)
  have eq := card_union_add_card_inter A B
  have c := card_le_univ M
  rw [card_compl,card_layout j X len] at all
  rw [card_layout j X len] at c
  change 2*sixWeight P.card j≤2*A.card+sixOverlap P.card j at a
  change B.card=rootWeight P.card j at b
  change (A∩B).card≤rootOverlap P.card j at d
  change (A∪B).card≤_ at all
  simp only [saving,if_true]
  omega
end WildSieve
