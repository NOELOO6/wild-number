import TripleCounts
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.Ring

namespace WildSieve.PartitionMoments
open Finset
variable {V : Type} [Fintype V] [DecidableEq V]

noncomputable def hits (H : Blocks V) {U : Finset V} (D : Layout U) := (D.val∩H).card
noncomputable def population (H : Blocks V) (U : Finset V) (f : Nat → Nat) :=
  ∑ D : Layout U, f (hits H D)

/-- Remove a specified triple. Every other hit remains, even when the removed triple
is itself a member of the forbidden family. -/
theorem peel (H : Blocks V) (S T : Finset V) (st : T⊆S) (sz : T.card=3) (f : Nat → Nat) :
    (∑ D : Layout S,if T∈D.val then f (hits H D-(if T∈H then 1 else 0)) else 0) =
      population H (S \ T) f := by
  classical
  let M : Blocks V := {T}
  have vm : vertices M=T := vertices_singleton _
  let e := completeEquiv S M (singleton_triple sz) (vm ▸ st)
  have eq : (∑ D : Layout S, if T∈D.val then f (hits H D-(if T∈H then 1 else 0)) else 0) =
      ∑ D : {D : Layout S // M⊆D.val}, f (hits H D.val-(if T∈H then 1 else 0)) := by
    rw [←sum_filter]
    apply Finset.sum_subtype
    simp [M]
  rw [eq,←vm]
  apply Fintype.sum_equiv e
  intro D
  have td := singleton_subset_iff.mp D.property
  change f (_-_) = f (((D.val.val \ M)∩H).card)
  congr 1
  unfold hits
  have same : (D.val.val \ M) ∩ H = (D.val.val∩H).erase T := by ext x; simp [M,and_left_comm,and_comm]
  rw [same,vm]
  by_cases yes : T∈H
  · rw [if_pos yes,card_erase_of_mem (mem_inter.mpr ⟨td,yes⟩)]
  · rw [if_neg yes,Nat.sub_zero,erase_eq_of_not_mem (fun h => yes (mem_inter.mp h).2)]

noncomputable def moment (H : Blocks V) (U : Finset V) (j : Nat) := population H U (fun h => h.choose j)

theorem moment_zero (H : Blocks V) (S : Finset V) (t : Nat) (sz : S.card=3*t) :
    moment H S 0=ways t := by simp [moment,population,card_layout t S sz]

/-- Double-count the choice of one forbidden block among j+1 distinct hits. -/
theorem moment_step (H : Blocks V) (S : Finset V) (j : Nat) :
    (j+1)*moment H S (j+1) =
      ∑ T∈(S.powersetCard 3 ∩ H),moment H (S\T) j := by
  classical
  let K := S.powersetCard 3 ∩ H
  have count (D : Layout S) : (K.filter (·∈D.val)).card=hits H D := by
    congr 1
    change _=D.val∩H
    ext T
    constructor
    · intro h
      exact mem_inter.mpr ⟨(mem_filter.mp h).2,(mem_inter.mp (mem_filter.mp h).1).2⟩
    · intro h
      obtain ⟨td,th⟩ := mem_inter.mp h
      have st : T⊆S := D.property.2 ▸ block_sub td
      exact mem_filter.mpr ⟨mem_inter.mpr ⟨mem_powersetCard.mpr ⟨st,D.property.1.size _ td⟩,th⟩,td⟩
  have row (D : Layout S) : (j+1)*(hits H D).choose (j+1)=
      ∑ T∈K,if T∈D.val then (hits H D-1).choose j else 0 := by
    rw [←sum_filter,sum_const,nsmul_eq_mul,count]
    cases hz : hits H D with
    | zero => simp
    | succ h =>
      simp only [Nat.add_one_sub_one]
      simpa [Nat.mul_comm] using (Nat.succ_mul_choose_eq h j).symm
  unfold moment population
  rw [mul_sum,sum_congr rfl (fun D _ => row D),sum_comm]
  apply sum_congr rfl
  intro T ht
  obtain ⟨st,sz⟩ := mem_powersetCard.mp (mem_inter.mp ht).1
  simpa only [if_pos (mem_inter.mp ht).2] using peel H S T st sz (fun h => h.choose j)


/-- The integer count of layouts that contain no forbidden triple. -/
noncomputable def avoiding (H : Blocks V) (S : Finset V) :=
  population H S (fun h => if h=0 then 1 else 0)

/-- Choose one of the t blocks of an avoiding layout, then forget it. -/
theorem avoiding_step (H : Blocks V) (S : Finset V) (t : Nat) (size : S.card=3*t) :
    t*avoiding H S = ∑ T∈(S.powersetCard 3 \ H),avoiding H (S\T) := by
  classical
  let K := S.powersetCard 3 \ H
  let f : Nat → Nat := fun h => if h=0 then 1 else 0
  have row (D : Layout S) : t*f (hits H D) =
      ∑ T∈K,if T∈D.val then f (hits H D) else 0 := by
    by_cases zero : hits H D=0
    · have empty : D.val∩H=∅ := card_eq_zero.mp zero
      have count : K.filter (·∈D.val)=D.val := by
        ext T
        refine ⟨fun h => (mem_filter.mp h).2,fun h => mem_filter.mpr ⟨mem_sdiff.mpr ⟨?_,?_⟩,h⟩⟩
        · exact mem_powersetCard.mpr ⟨D.property.2 ▸ block_sub h,D.property.1.size _ h⟩
        · intro th
          have both := mem_inter.mpr ⟨h,th⟩
          rw [empty] at both
          simp at both
      rw [←sum_filter,count,sum_const,nsmul_eq_mul]
      have cards := D.property.1.card_vertices
      rw [D.property.2,size] at cards
      have eq : D.val.card=t := by omega
      simp [eq]
    · simp [f,zero]
  unfold avoiding population
  rw [mul_sum,sum_congr rfl (fun D _ => row D),sum_comm]
  apply sum_congr rfl
  intro T ht
  obtain ⟨st,sz⟩ := mem_powersetCard.mp (mem_sdiff.mp ht).1
  simpa only [if_neg (mem_sdiff.mp ht).2,Nat.sub_zero] using peel H S T st sz f

private theorem partial_succ (h k : Nat) :
    (∑ i∈range (k+1),(-1 : ℤ)^i * ((h+1).choose i : ℤ)) = (-1 : ℤ)^k * (h.choose k : ℤ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ,ih,Nat.choose_succ_succ,Nat.cast_add,pow_succ]
    ring

/-- The signed binomial sum on any layout has the Bonferroni sign. The excess
is given exactly by one binomial coefficient whenever the layout has a hit. -/
theorem partial_hits (h k : Nat) :
    (∑ i∈range (k+1),(-1 : ℤ)^i * (h.choose i : ℤ)) =
      (if h=0 then 1 else (-1 : ℤ)^k * ((h-1).choose k : ℤ)) := by
  cases h with
  | zero =>
    simp only [if_pos rfl]
    induction k with
    | zero => simp
    | succ k ih => rw [sum_range_succ,ih]; simp
  | succ h => simpa only [Nat.succ_ne_zero,if_false,Nat.add_one_sub_one] using partial_succ h k

noncomputable def partialMoment (H : Blocks V) (S : Finset V) (k : Nat) : ℤ :=
  ∑ i∈range (k+1),(-1 : ℤ)^i * (moment H S i : ℤ)

private theorem partial_layouts (H : Blocks V) (S : Finset V) (k : Nat) :
    partialMoment H S k = ∑ D : Layout S,
      if hits H D=0 then 1 else (-1 : ℤ)^k * (((hits H D-1).choose k) : ℤ) := by
  classical
  unfold partialMoment moment population
  simp only [Nat.cast_sum,mul_sum]
  rw [sum_comm]
  exact sum_congr rfl (fun D _ => partial_hits (hits H D) k)

theorem bonferroni (H : Blocks V) (S : Finset V) (k : Nat) :
    partialMoment H S (2*k+1) ≤ (avoiding H S : ℤ) ∧
    (avoiding H S : ℤ) ≤ partialMoment H S (2*k) := by
  classical
  rw [partial_layouts,partial_layouts]
  unfold avoiding population
  push_cast
  constructor <;> apply sum_le_sum <;> intro D _
  all_goals by_cases h : hits H D=0 <;> simp [h,pow_add,pow_mul]

#print axioms avoiding_step
#print axioms bonferroni

end WildSieve.PartitionMoments
