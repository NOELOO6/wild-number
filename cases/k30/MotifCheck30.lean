import EdgeDeletion
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.FinRange

namespace WildSieve.Thirty.Motifs
open Finset WildSieve.EdgeDeletion

def nodes {α : Type} [DecidableEq α] (T : Finset (Finset α)) := T.biUnion id

def center {α : Type} [DecidableEq α] (T : Finset (Finset α)) : Bool :=
  decide (∃ v∈nodes T, ∀ e∈T,v∈e)

/-- Six times the penalty on an unordered pair of distinct edges. -/
def pairCost {α : Type} [DecidableEq α] (p : Finset (Finset α)) : Nat :=
  if (nodes p).card=4 then 5 else 4

/-- Six times the rebate on an unordered triple of distinct edges. In order
of decreasing support, the types are matching, wedge plus edge, path or star,
and triangle. -/
def tripleCredit {α : Type} [DecidableEq α] (p : Finset (Finset α)) : Nat :=
  match (nodes p).card with
  | 3 => 0
  | 4 => if center p then 3 else 2
  | _ => 3

def wins {α : Type} [DecidableEq α] (S : Finset (Finset α)) : Bool :=
  decide (S.card=0 ∨ 6+bill pairCost 2 S≤6*S.card+bill tripleCredit 3 S)

/-- Stream the small subsets with bounded memory. -/
def sweep {α : Type} [DecidableEq α] (test : Finset α → Bool) :
    List α → Finset α → Nat → Bool
  | [], S, _ => test S
  | _::_, S, 0 => test S
  | a::as, S, room+1 =>
      sweep test as S (room+1) && sweep test as (insert a S) room

theorem sweep_sound {α : Type} [DecidableEq α] (test : Finset α → Bool) (l : List α)
    (S T : Finset α) (room : Nat) (sub : T⊆l.toFinset) (fit : T.card≤room)
    (pass : sweep test l S room=true) : test (S∪T)=true := by
  classical
  induction l generalizing S T room with
  | nil =>
    have eq : T=∅ := by simpa using sub
    simpa [eq] using pass
  | cons a l ih =>
    rw [List.toFinset_cons] at sub
    cases room with
    | zero =>
      have eq : T=∅ := card_eq_zero.mp (by omega)
      simpa [eq] using pass
    | succ k =>
      obtain ⟨skip,use⟩ := Bool.and_eq_true_iff.mp pass
      by_cases h : a∈T
      · have tail : T.erase a⊆l.toFinset := by
          intro x hx
          exact (mem_insert.mp (sub (mem_of_mem_erase hx))).resolve_left (mem_erase.mp hx).1
        have small : (T.erase a).card≤k := by rw [card_erase_of_mem h]; omega
        have eq : insert a S∪T.erase a=S∪T := by
          ext x
          by_cases same : x=a
          · subst x; simp [h]
          · simp [same]
        exact eq ▸ ih _ _ _ tail small use
      · have tail : T⊆l.toFinset := by
          intro x hx
          exact (mem_insert.mp (sub hx)).resolve_left (fun e => h (e ▸ hx))
        exact ih _ _ _ tail fit skip

def deck : List (Finset (Fin 10)) := do
  let a ← List.finRange 10
  let b ← List.finRange 10
  guard (a<b)
  pure {a,b}

theorem mem_deck {e : Finset (Fin 10)} (size : e.card=2) : e∈deck := by
  obtain ⟨a,b,ab,rfl⟩ := card_eq_two.mp size
  rcases lt_or_gt_of_ne ab with h|h
  · simp [deck,List.bind_eq_flatMap,List.mem_flatMap,guard]
    exact ⟨a,b,by simp [h],rfl⟩
  · simp [deck,List.bind_eq_flatMap,List.mem_flatMap,guard]
    exact ⟨b,a,by simp [h],Finset.pair_comm _ _⟩

end WildSieve.Thirty.Motifs
