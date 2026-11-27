import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace WildExact.Seventeen
open Finset
abbrev C := Fin 17

def other (a b : C) := (univ.erase a).erase b
def ordered2 (f : C → C → Int) : Int := ∑ a,∑ b ∈ univ.erase a,f a b
def ordered3 (f : C → C → C → Int) : Int := ordered2 (fun a b => ∑ c ∈ other a b,f a b c)

private theorem expand3 (f : C → C → C → Int) :
    ordered3 f = ∑ a,∑ b,∑ c,if a≠b ∧ b≠c ∧ c≠a then f a b c else 0 := by
  unfold ordered3 ordered2 other
  apply sum_congr rfl
  intro a _
  have filt : (univ.filter fun y : C => y≠a)=univ.erase a := by ext; simp
  rw [←filt, sum_filter]
  apply sum_congr rfl
  intro b _
  by_cases ab : a=b
  · subst b; simp
  · rw [if_pos (Ne.symm ab)]
    have pick : ((univ.erase a).erase b) = univ.filter (fun c : C => a≠b ∧ b≠c ∧ c≠a) := by
      ext c; simp [ab,ne_comm]
    dsimp only
    rw [pick,sum_filter]

private theorem fullCycle (f : C → C → C → Int) :
    (∑ a,∑ b,∑ c,f a b c) = ∑ b,∑ c,∑ a,f a b c := by
  rw [sum_comm]
  apply sum_congr rfl
  intro b _
  exact sum_comm

theorem cycle3 (f : C → C → C → Int) : ordered3 f = ordered3 (fun a b c => f b c a) := by
  rw [expand3,expand3,←fullCycle]
  apply sum_congr rfl; intro a _
  apply sum_congr rfl; intro b _
  apply sum_congr rfl; intro c _
  simp only [and_comm,and_left_comm,and_assoc]

theorem moment_scalar (s : Finset C) :
    12*(1-(s.card:Int))+5*((s.card*((s.card)-1):Nat):Int)-
       ((s.card*(s.card-1)*(s.card-2):Nat):Int) ≤ 12*(if s.card=0 then 1 else 0) := by
  have bound : s.card≤17 := by simpa using s.card_le_univ
  exact (show ∀ n : Fin 18,12*(1-(n.val:Int))+5*((n.val*(n.val-1):Nat):Int)-
    ((n.val*(n.val-1)*(n.val-2):Nat):Int) ≤ 12*(if n.val=0 then 1 else 0) from by decide) ⟨s.card,by omega⟩

private theorem filter_sums (s : Finset C) (f : C → Int) :
    (∑ x,if x∈s then f x else 0)=∑ x∈s,f x := by rw [←sum_filter]; simp

theorem one_moment (s : Finset C) : (∑ a : C,if a∈s then (1:Int) else 0)=s.card := by
  rw [filter_sums]; simp

private theorem onErase (s : Finset C) (a : C) (f : C → Int) :
    (∑ x∈univ.erase a,if x∈s then f x else 0)=∑ x∈s.erase a,f x := by
  rw [←sum_filter]
  congr 1; ext x; simp [and_comm]

private theorem onOther (s : Finset C) (a b : C) :
    (∑ x∈other a b,if x∈s then (1:Int) else 0)=((s.erase a).erase b).card := by
  rw [←sum_filter]
  have eq : (other a b).filter (·∈s)=(s.erase a).erase b := by ext; simp [other,and_assoc,and_left_comm,and_comm]
  simp [eq]

theorem two_moment (s : Finset C) :
    ordered2 (fun a b => if a∈s ∧ b∈s then 1 else 0)=((s.card*(s.card-1):Nat):Int) := by
  unfold ordered2
  have row (a : C) : (∑ b∈univ.erase a,if a∈s ∧ b∈s then (1:Int) else 0)=
      if a∈s then ((s.card-1:Nat):Int) else 0 := by
    by_cases ha : a∈s
    · simp only [ha,true_and,if_true,onErase]; simp [card_erase_of_mem ha]
    · simp [ha]
  simp_rw [row]
  rw [filter_sums]
  simp [nsmul_eq_mul]

theorem three_moment (s : Finset C) :
    ordered3 (fun a b c => if a∈s ∧ b∈s ∧ c∈s then 1 else 0)=
      ((s.card*(s.card-1)*(s.card-2):Nat):Int) := by
  unfold ordered3 ordered2
  have row (a b : C) (hb : b∈univ.erase a) :
      (∑ c∈other a b,if a∈s ∧ b∈s ∧ c∈s then (1:Int) else 0)=
        if a∈s ∧ b∈s then ((s.card-2:Nat):Int) else 0 := by
    by_cases h : a∈s ∧ b∈s
    · have yes : b∈s.erase a := mem_erase.mpr ⟨(mem_erase.mp hb).1,h.2⟩
      simp only [h.1,h.2,true_and,if_true,onOther,card_erase_of_mem yes,card_erase_of_mem h.1]
      rfl
    · by_cases ha : a∈s <;> simp_all
  have outer (a : C) : (∑ b∈univ.erase a, ∑ c∈other a b,if a∈s ∧ b∈s ∧ c∈s then (1:Int) else 0)=
      if a∈s then ((s.card-1:Nat):Int)*((s.card-2:Nat):Int) else 0 := by
    rw [sum_congr rfl (row a)]
    by_cases ha : a∈s
    · simp only [ha,true_and,if_true,onErase]; simp [card_erase_of_mem ha,nsmul_eq_mul]
    · simp [ha]
  simp_rw [outer]
  rw [filter_sums]
  simp [nsmul_eq_mul,mul_assoc]

end WildExact.Seventeen
