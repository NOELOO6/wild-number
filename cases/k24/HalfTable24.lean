import HalfProfiles24
import Mathlib.Data.Multiset.Replicate

namespace WildSieve.TwentyFour
open Finset WildAnchor
local instance (priority := 2000) tableEq {n : Nat} : DecidableEq (Fin n) := (inferInstance : LinearOrder (Fin n)).toDecidableEq

/-- Four endpoint populations in the true half, determined by the size k of
the false half and the number s of indices simultaneously incident to both colors. -/
def tagList (m k s : Nat) :=
  List.replicate (m+s-2*k) (false,false) ++ List.replicate (k-s) (false,true) ++
  List.replicate (k-s) (true,false) ++ List.replicate s (true,true)

def overlapSize {m : Nat} (p : Equiv.Perm (Fin m)) (X : Finset (Fin m)) :=
  (X∩X.map p.toEmbedding).card

theorem tag_populations {m : Nat} (p : Equiv.Perm (Fin m)) (X : Finset (Fin m)) :
    (univ : Finset (Fin m)).val.map (edgeBits p X)=
      (tagList m X.card (overlapSize p X) : Multiset (Bool × Bool)) := by
  let Y := X.map p.toEmbedding
  let s := (X∩Y).card
  have y : Y.card=X.card := card_map _
  have counts (x z : Bool) :
      ((univ : Finset (Fin m)).val.map (edgeBits p X)).count (x,z) =
      (univ.filter (fun i => edgeBits p X i=(x,z))).card := by
    simp only [Multiset.count_eq_card_filter_eq,Multiset.filter_map,Multiset.card_map]
    congr 1
    ext i
    simp [eq_comm,Function.comp_def]
  have regions : (univ.filter (fun i => edgeBits p X i=(false,false)))=(X∪Y)ᶜ ∧
      (univ.filter (fun i => edgeBits p X i=(false,true)))=Y \ X ∧
      (univ.filter (fun i => edgeBits p X i=(true,false)))=X \ Y ∧
      (univ.filter (fun i => edgeBits p X i=(true,true)))=X∩Y := by
    refine ⟨?_,?_,?_,?_⟩ <;> ext i <;> simp [edgeBits,Y,and_comm]
  have join := card_union_add_card_inter X Y
  have left := card_sdiff_add_card_inter X Y
  have right := card_sdiff_add_card_inter Y X
  rw [inter_comm Y X] at right
  apply Multiset.ext.mpr
  rintro ⟨a,b⟩
  rw [counts]
  cases a <;> cases b
  all_goals simp only [Multiset.coe_count,tagList,List.count_append,List.count_replicate]
  all_goals conv_rhs => simp
  · rw [regions.1,card_compl,Fintype.card_fin]
    change m-(X∪Y).card=m+(X∩Y).card-2*X.card
    omega
  · rw [regions.2.1]
    change (Y \ X).card=X.card-(X∩Y).card
    omega
  · rw [regions.2.2.1]
    change (X \ Y).card=X.card-(X∩Y).card
    omega
  · rw [regions.2.2.2]
    rfl

/-- A mathematical entry of the conditional histogram, defined by the
sublists of a twelve-element list with multiplicities. -/
def conditionalCell (m k s v a b : Nat) :=
  ((((tagList m k s : Multiset (Bool × Bool))).powersetCard v).map totals).count (a,b)

theorem conditional_correct {m : Nat} (p : Equiv.Perm (Fin m)) (X : Finset (Fin m))
    (v a b : Nat) :
    (((univ : Finset (Fin m)).powersetCard v).filter
      (fun Y => (Y∩X).card=a ∧ (Y∩X.map p.toEmbedding).card=b)).card =
    conditionalCell m X.card (overlapSize p X) v a b := by
  have spectrum := subset_profile p X v
  rw [tag_populations] at spectrum
  have eq := congrArg (Multiset.count (a,b)) spectrum
  rw [Multiset.count_eq_card_filter_eq,Multiset.filter_map,Multiset.card_map] at eq
  change (((univ : Finset (Fin m)).powersetCard v).filter (fun Y => (a,b)=((Y∩X).card,(Y∩X.map p.toEmbedding).card))).card=_ at eq
  convert eq using 1
  · congr 1
    ext Y
    simp [Function.comp_def,eq_comm,and_comm]
end WildSieve.TwentyFour
