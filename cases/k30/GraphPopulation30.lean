import SixCounts30
import Population30

namespace WildSieve.Thirty.Graph
open Finset
local instance (priority := 2000) populationEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq

private def fiber {α : Type} [Fintype α] {m : Nat} (f : α → Fin m) (i : Fin m) : Nat :=
  (univ.filter fun c => f c=i).card

private theorem count_fibers {α : Type} [Fintype α] {m : Nat} (f : α → Fin m) (w : Fin m → Nat) :
    ∑ i,w i*fiber f i = ∑ c,w (f c) := by
  classical
  have one (i : Fin m) : w i*fiber f i=∑ c : α, if f c=i then w i else 0 := by
    rw [←sum_filter,sum_const,nsmul_eq_mul,Nat.mul_comm]
    rfl
  simp_rw [one]
  rw [sum_comm]
  simp

def leftType (F : Factor V C) (L : Finset V) (size : L.card=12) (c : C) : Fin 7 :=
  ⟨Inside F c L,by have := (inside_window F c L).2; omega⟩

def cutPopulation (F : Factor V C) (L : Finset V) (size : L.card=12) (i : Fin 7) : ℚ :=
  fiber (leftType F L size) i

theorem cut_population_sum (F : Factor V C) (L : Finset V) (sz : L.card=12) (w : Fin 7 → ℚ) :
    ∑ i,w i*cutPopulation F L sz i = ∑ c,w (leftType F L sz c) := by
  classical
  have one (i : Fin 7) : w i*cutPopulation F L sz i =
      ∑ c : C,if leftType F L sz c=i then w i else 0 := by
    rw [←sum_filter,sum_const,nsmul_eq_mul,mul_comm]
    rfl
  simp_rw [one]
  rw [sum_comm]
  simp

/-- Every closed twelve-set in every K30 factorization generates a population
with total 29, first moment 66 and at least one closing color. -/
theorem cut_population_valid (F : Factor V C) (L : Finset V) (size : L.card=12)
    (a : C) (cl : Closed (F.f a) L) : Population (cutPopulation F L size) := by
  have total := count_fibers (leftType F L size) (fun _ => 1)
  have edges := count_fibers (leftType F L size) Fin.val
  simp only [one_mul,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.mul_one] at total
  change _=∑ c,Inside F c L at edges
  rw [sum_inside,size] at edges
  have cs := closed_size (F.invol a) (F.moving a) cl
  change L.card=2*Inside F a L at cs
  have six : leftType F L size a=6 := Fin.ext (by change Inside F a L=6; omega)
  have pos : 0<fiber (leftType F L size) 6 :=
    card_pos.mpr ⟨a,mem_filter.mpr ⟨mem_univ _,six⟩⟩
  constructor
  · intro i; exact Nat.cast_nonneg _
  · unfold cutPopulation; exact_mod_cast total
  · unfold cutPopulation; exact_mod_cast edges
  · unfold cutPopulation; exact_mod_cast pos

private def sixType (F : Factor V C) (S : Finset V) (size : S.card=6) (c : C) : Fin 4 :=
  ⟨Inside F c S,by have := (inside_window F c S).2; omega⟩

private noncomputable def duplicateFiber (F : Factor V C) (S : Finset V) (i : Fin 4) : Nat :=
  extra F S*((univ : Finset C).filter (fun c => Inside F c S=i.val)).card

noncomputable def duplicatePopulation (F : Factor V C) (i : Fin 4) : Nat :=
  ∑ S∈marks F univ,duplicateFiber F S i

private theorem dup_local (F : Factor V C) (S : Finset V) (sz : S.card=6) (w : Fin 4 → Nat) :
    ∑ i,w i*duplicateFiber F S i = extra F S*∑ c,w (sixType F S sz c) := by
  classical
  have count (i : Fin 4) : duplicateFiber F S i=extra F S*fiber (sixType F S sz) i := by
    unfold duplicateFiber fiber
    congr 2
    ext c
    simp [sixType,Fin.ext_iff]
  simp_rw [count,mul_left_comm (w _) (extra F S)]
  rw [←mul_sum,count_fibers]

theorem duplicate_totals (F : Factor V C) :
    (∑ i : Fin 4,duplicatePopulation F i)=29*defect F ∧
    (∑ i : Fin 4,i.val*duplicatePopulation F i)=15*defect F ∧
    2*defect F≤duplicatePopulation F 3 := by
  classical
  have tally (w : Fin 4 → Nat) :
      (∑ i,w i*duplicatePopulation F i)=∑ S∈marks F univ,∑ i,w i*duplicateFiber F S i := by
    simp only [duplicatePopulation,mul_sum]
    rw [sum_comm]
  have group (u : Nat) : (∑ S∈marks F univ,extra F S*u)=u*defect F := by
    rw [←sum_mul,(full_defect F).1,Nat.mul_comm]
  constructor
  · have h := tally (fun _ => 1)
    simp only [one_mul] at h
    rw [h,←group 29]
    apply sum_congr rfl
    intro S hs
    simpa using dup_local F S (mark_mem.mp hs).2.1 (fun _ => 1)
  constructor
  · rw [tally Fin.val,←group 15]
    apply sum_congr rfl
    intro S hs
    have sz := (mark_mem.mp hs).2.1
    have h := dup_local F S sz Fin.val
    change _=extra F S*∑ c,Inside F c S at h
    rw [sum_inside,sz] at h
    exact h
  · rw [←group 2]
    apply sum_le_sum
    intro S hs
    have sz := (mark_mem.mp hs).2.1
    have sub : owners F S⊆(univ : Finset C).filter (fun c => Inside F c S=(3 : Fin 4).val) := by
      intro c hc
      have h := closed_size (F.invol c) (F.moving c) (owner_mem.mp hc)
      change S.card=2*Inside F c S at h
      exact mem_filter.mpr ⟨mem_univ _,by change Inside F c S=3; omega⟩
    by_cases zero : extra F S=0
    · simp [duplicateFiber,zero]
    · have many : 2≤(owners F S).card := by
        change (owners F S).card-1≠0 at zero
        omega
      exact Nat.mul_le_mul_left _ (many.trans (card_le_card sub))

theorem duplicate_population_sum (F : Factor V C) (w : Nat → ℚ) :
    (∑ i : Fin 4,w i*(duplicatePopulation F i : ℚ))=
      ∑ S∈marks F univ,(extra F S : ℚ)*∑ c,w (Inside F c S) := by
  classical
  simp only [duplicatePopulation,Nat.cast_sum,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro S hs
  have sz := (mark_mem.mp hs).2.1
  have one (i : Fin 4) : w i*(duplicateFiber F S i : ℚ)=
      (extra F S : ℚ)*∑ c : C,if sixType F S sz c=i then w i else 0 := by
    rw [←sum_filter,sum_const,nsmul_eq_mul]
    have same : univ.filter (fun c => sixType F S sz c=i)=
        univ.filter (fun c => Inside F c S=i.val) := by
      ext c; simp [sixType,Fin.ext_iff]
    rw [same,duplicateFiber,Nat.cast_mul]
    ring
  simp_rw [one]
  rw [←mul_sum,sum_comm]
  simp [sixType,mul_sum]

#print axioms cut_population_valid
#print axioms duplicate_totals
end WildSieve.Thirty.Graph
