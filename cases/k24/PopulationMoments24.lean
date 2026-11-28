import GraphRegions24
import GraphTable24

namespace WildSieve.TwentyFour
open Finset WildExact
local instance (priority := 2000) momentsEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq

private theorem marked_row (F : Factor V C) (S : Finset V) (i j : Nat) :
    popAt F S i*(popAt F S j-(if i=j then 1 else 0))=
      ∑ a : C,∑ c∈univ.erase a,if Inside F a S=i ∧ Inside F c S=j then 1 else 0 := by
  classical
  let X := univ.filter (fun a : C => Inside F a S=i)
  let Y := univ.filter (fun c : C => Inside F c S=j)
  have row (a : C) : (∑ c∈univ.erase a,if Inside F a S=i ∧ Inside F c S=j then 1 else 0)=
      if a∈X then Y.card-(if i=j then 1 else 0) else 0 := by
    rw [←Finset.card_filter]
    by_cases hx : a∈X
    · have yes := (mem_filter.mp hx).2
      have eq : (univ.erase a).filter (fun c => Inside F a S=i ∧ Inside F c S=j)=Y.erase a := by
        ext c; simp [Y,yes,and_comm]
      rw [eq,if_pos hx]
      by_cases h : i=j
      · have inside : a∈Y := mem_filter.mpr ⟨mem_univ _,yes.trans h⟩
        rw [if_pos h,card_erase_of_mem inside]
      · have no : a∉Y := fun y => h (yes.symm.trans (mem_filter.mp y).2)
        rw [if_neg h,erase_eq_of_not_mem no,Nat.sub_zero]
    · have no : Inside F a S≠i := fun h => hx (mem_filter.mpr ⟨mem_univ _,h⟩)
      simp [no,hx]
  simp_rw [row]
  rw [←sum_filter,sum_const,nsmul_eq_mul]
  simp [X,Y,popAt]

/-- The entire quadratic population on the u-sets counts ordered pairs of
distinct colors, with their genuine two-matching subset histograms. -/
theorem quadratic_sum (g : Coloring 24 23) (u i j : Nat) :
    (∑ S∈(univ : Finset V).powersetCard u,
      popAt (coloringFactor g) S i*(popAt (coloringFactor g) S j-(if i=j then 1 else 0)))=
      ∑ a : C,∑ c∈univ.erase a,graphCell g a c u i j := by
  classical
  simp_rw [marked_row]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  rw [sum_comm]
  apply sum_congr rfl
  intro c _
  rw [←Finset.card_filter]
  apply congrArg Finset.card
  ext S
  simp [graphCell]

#print axioms quadratic_sum
end WildSieve.TwentyFour
