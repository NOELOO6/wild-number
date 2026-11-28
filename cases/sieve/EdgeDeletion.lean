import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace WildSieve.EdgeDeletion
open Finset
variable {α : Type} [DecidableEq α]

def bill (w : Finset α → Nat) (k : Nat) (S : Finset α) := ∑ T∈S.powersetCard k,w T

/-- Each configuration of k edges survives exactly |S|-k single-edge deletions. -/
theorem deletion_sum (w : Finset α → Nat) (k : Nat) (S : Finset α) :
    (∑ e∈S,bill w k (S.erase e))=(S.card-k)*bill w k S := by
  classical
  have per (e : α) : (S.erase e).powersetCard k=(S.powersetCard k).filter (fun T => e∉T) := by
    ext T
    simp only [mem_powersetCard,mem_filter]
    constructor
    · rintro ⟨sub,sz⟩
      exact ⟨⟨sub.trans (erase_subset _ _),sz⟩,fun h => not_mem_erase _ _ (sub h)⟩
    · rintro ⟨⟨sub,sz⟩,no⟩
      exact ⟨fun x hx => mem_erase.mpr ⟨fun eq => no (eq ▸ hx),sub hx⟩,sz⟩
  have row (T) (h : T∈S.powersetCard k) :
      (∑ e∈S,if e∉T then w T else 0)=(S.card-k)*w T := by
    rw [←sum_filter,sum_const,nsmul_eq_mul]
    have eq : S.filter (·∉T)=S \ T := by ext e; simp
    rw [eq,card_sdiff (mem_powersetCard.mp h).1,(mem_powersetCard.mp h).2,Nat.cast_id]
  simp only [bill,per,sum_filter]
  rw [sum_comm,sum_congr rfl row,mul_sum]

/-- An inequality for all nonempty edge sets with at most five edges lifts to
arbitrary edge sets. Every pair must carry a penalty of at least four. -/
theorem lift_five (q b : Finset α → Nat) (S : Finset α)
    (cost : ∀ p∈S.powersetCard 2,4≤q p)
    (base : ∀ T⊆S, 0<T.card → T.card≤5 → 6+bill q 2 T≤6*T.card+bill b 3 T)
    (nonempty : 0<S.card) : 6+bill q 2 S≤6*S.card+bill b 3 S := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases small : S.card≤5
    · exact base S Subset.rfl nonempty small
    have many : 6≤S.card := by omega
    have each (e : α) (he : e∈S) : 6+bill q 2 (S.erase e)≤6*(S.card-1)+bill b 3 (S.erase e) := by
      rw [←card_erase_of_mem he]
      exact ih _ (erase_ssubset he) (fun p hp => cost p
        (mem_powersetCard.mpr ⟨(mem_powersetCard.mp hp).1.trans (erase_subset _ _),(mem_powersetCard.mp hp).2⟩))
        (fun T h => base T (h.trans (erase_subset _ _))) (by rw [card_erase_of_mem he]; omega)
    have all := sum_le_sum each
    rw [sum_add_distrib,sum_add_distrib,deletion_sum,deletion_sum,sum_const,sum_const] at all
    simp only [nsmul_eq_mul,Nat.cast_id] at all
    have qq := sum_le_sum (s:=S.powersetCard 2) cost
    simp only [sum_const,nsmul_eq_mul,card_powersetCard] at qq
    change S.card.choose 2*4≤bill q 2 S at qq
    have choose : S.card.choose 2*2=S.card*(S.card-1) := by
      rw [Nat.choose_two_right]
      exact Nat.div_mul_cancel (Nat.even_mul_pred_self S.card).two_dvd
    have qlower : 12*(S.card-1)≤bill q 2 S := by
      nlinarith only [qq,choose,Nat.mul_le_mul_right (S.card-1) many]
    apply le_of_not_gt
    intro fail
    have pp := Nat.mul_lt_mul_of_pos_left fail (show 0<S.card-3 by omega)
    have s1 : S.card-1=(S.card-3)+2 := by omega
    have s2 : S.card-2=(S.card-3)+1 := by omega
    have s3 : S.card=(S.card-3)+3 := by omega
    generalize S.card-3=z at *
    rw [s1,s2,s3] at all
    rw [s3] at pp
    rw [s1] at qlower
    nlinarith only [all,pp,qlower]

end WildSieve.EdgeDeletion
