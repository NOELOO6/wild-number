import PieceTotals
import SmallAverage
namespace WildPieces
open Finset
abbrev Perm19 := Equiv.Perm V
def cost (p : Perm19) := deficit (components p)

theorem single_color : 19 * (∑ p : Perm19, cost p) < 243290200817664000 :=
  aggregate cost (fun p => waysSplit 2 (components p)) (fun p => waysSplit 3 (components p))
    (fun p => waysSplit 4 (components p)) (fun p => split_bound (components p))
    ((sum_splits 2).trans two_cells) ((sum_splits 3).trans three_cells) ((sum_splits 4).trans four_cells)

theorem choose_thirteen (q : V → Perm19) : ∃ p : Perm19, ∑ c, deficit (components (p*q c)) ≤ 1 := by
  have rotate (c : V) : (∑ p : Perm19, cost (p*q c)) = ∑ p : Perm19, cost p :=
    Fintype.sum_equiv (Equiv.mulRight (q c)) (fun p => cost (p*q c)) cost (fun _ => rfl)
  apply pivot (fun c p => cost (p*q c)) (∑ p : Perm19, cost p) rotate
  have n : Fintype.card V = 19 := Fintype.card_fin 19
  have np : Fintype.card Perm19 = (19 : Nat).factorial :=
    (Fintype.card_perm (α:=V)).trans (congrArg Nat.factorial n)
  have size : (19 : Nat).factorial*2 = 243290200817664000 := by decide +kernel
  exact lt_of_eq_of_lt (congrArg (· * ∑ p : Perm19, cost p) n)
    (lt_of_lt_of_eq single_color ((congrArg (·*2) np).trans size).symm)
end WildPieces
