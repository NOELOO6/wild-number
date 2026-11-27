import Avoidance
import Mathlib.Tactic.FieldSimp

namespace WildSieve
open Finset
variable {L R : Type} [Fintype L] [Fintype R] [Nonempty R]

/-- A finite coupling with a uniform left marginal and a uniform right
marginal. A left outcome may have any positive number of compatible right
outcomes. Relabelings make their total incoming weights equal. -/
theorem uniform_coupling (rel : L → R → Prop) (exists_right : ∀ x, ∃ y, rel x y)
    (sym : ∀ y z : R, ∃ (f : L ≃ L) (g : R ≃ R), g y=z ∧ ∀ x w, rel x w ↔ rel (f x) (g w))
    (A : Finset L) (B : Finset R) (keeps : ∀ x y, rel x y → y ∈ B → x ∈ A) :
    (B.card : ℚ) * Fintype.card L ≤ (A.card : ℚ) * Fintype.card R := by
  classical
  let row (x : L) := univ.filter (rel x)
  let w (x : L) (y : R) : ℚ := if rel x y then 1 / (row x).card else 0
  have rowpos (x) : 0 < (row x).card := card_pos.mpr (by
    obtain ⟨y,hy⟩ := exists_right x
    exact ⟨y,mem_filter.mpr ⟨mem_univ _,hy⟩⟩)
  have norm (x) : ∑ y, w x y = 1 := by
    have nz : ((row x).card : ℚ) ≠ 0 := by exact_mod_cast (rowpos x).ne'
    simp only [w,← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,one_div]
    exact mul_inv_cancel₀ nz
  let column (y : R) : ℚ := ∑ x, w x y
  have same (y z) : column y=column z := by
    obtain ⟨f,g,gy,h⟩ := sym y z
    apply Fintype.sum_equiv f
    intro x
    have d : (row x).card = (row (f x)).card := by
      apply card_bij (fun b _ => g b)
      · intro b hb
        exact mem_filter.mpr ⟨mem_univ _,(h x b).mp (mem_filter.mp hb).2⟩
      · exact fun _ _ _ _ eq => g.injective eq
      · intro a ha
        refine ⟨g.symm a,mem_filter.mpr ⟨mem_univ _,(h _ _).mpr ?_⟩,g.apply_symm_apply _⟩
        simpa using (mem_filter.mp ha).2
    simp only [w,d,← gy,← h]
  let r : R := Classical.choice ‹Nonempty R›
  have total : (Fintype.card R : ℚ) * column r = Fintype.card L := by
    calc
      _ = ∑ y : R, column y := by simp [fun y => same y r]
      _ = ∑ x, ∑ y, w x y := Finset.sum_comm
      _ = _ := by simp [norm]
  have part : (B.card : ℚ) * column r ≤ A.card := by
    calc
      _ = ∑ y ∈ B, column y := by simp [fun y => same y r]
      _ = ∑ x, ∑ y ∈ B, w x y := Finset.sum_comm
      _ ≤ ∑ x : L, if x ∈ A then (1 : ℚ) else 0 := by
        apply sum_le_sum
        intro x _
        by_cases hx : x ∈ A
        · rw [if_pos hx,← norm x]
          exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => by unfold w; split; exact div_nonneg zero_le_one (Nat.cast_nonneg _); exact le_rfl)
        · rw [if_neg hx]
          apply le_of_eq
          apply sum_eq_zero
          intro y hy
          exact if_neg (fun h => hx (keeps x y h hy))
      _ = _ := by simp
  rw [← total]
  calc
    _ = ((B.card : ℚ) * column r) * Fintype.card R := by ac_rfl
    _ ≤ _ := mul_le_mul_of_nonneg_right part (Nat.cast_nonneg _)

end WildSieve
