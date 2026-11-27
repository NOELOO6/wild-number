import DecreasingTriples
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Logic.Equiv.Basic

namespace WildSlots
open Finset WildDeletion WildExact

/-- The permutations fitting one consistent binary pattern occupy at least
the reciprocal of the middle binomial coefficient of all permutations. -/
private theorem fraction {n : Nat} (a b : Fin n → Bool) (p : Perm (Fin n)) (good : fits a b p) :
    Fintype.card (Perm (Fin n)) ≤
    (univ.filter (fits a b)).card * n.choose (n/2) := by
  let A (i : Fin n) := a i=true
  let left := {i : Fin n // A i}
  let right := {i : Fin n // ¬A i}
  let make (q : Perm left × Perm right) := (q.1.subtypeCongr q.2).trans p
  have keep (q : Perm left × Perm right) (i : Fin n) : a (q.1.subtypeCongr q.2 i)=a i := by
    by_cases h : A i
    · rw [Equiv.Perm.subtypeCongr.left_apply _ _ h]
      exact (q.1 ⟨i,h⟩).property.trans h.symm
    · rw [Equiv.Perm.subtypeCongr.right_apply _ _ h]
      exact (Bool.eq_false_iff.mpr (q.2 ⟨i,h⟩).property).trans (Bool.eq_false_iff.mpr h).symm
  let f (q : Perm left × Perm right) : ↥(univ.filter (fits a b)) :=
    ⟨make q,mem_filter.mpr ⟨mem_univ _,fun i => (keep q i).symm.trans (good _)⟩⟩
  have inj : Function.Injective f := by
    intro q r eq
    have h (x : Fin n) : q.1.subtypeCongr q.2 x=r.1.subtypeCongr r.2 x :=
      p.injective (congrArg (fun t : ↥(univ.filter (fits a b)) => t.val x) eq)
    apply Prod.ext
    · apply Equiv.ext
      intro x
      exact Subtype.ext (by simpa only [Equiv.Perm.subtypeCongr.left_apply_subtype] using h x.val)
    · apply Equiv.ext
      intro x
      exact Subtype.ext (by simpa only [Equiv.Perm.subtypeCongr.right_apply_subtype] using h x.val)
  let k := Fintype.card left
  have kc : k≤n := by simpa [k,left] using Fintype.card_subtype_le A
  have kr : Fintype.card right=n-k := by simp [right,left,k,Fintype.card_subtype_compl]
  have count := Fintype.card_le_of_injective f inj
  simp only [Fintype.card_prod,Fintype.card_perm,Fintype.card_coe,kr] at count
  have bound := Nat.mul_le_mul count (Nat.choose_le_middle k n)
  rw [Fintype.card_perm,Fintype.card_fin]
  calc
    n.factorial = (k.factorial*(n-k).factorial)*n.choose k := by
      rw [←Nat.choose_mul_factorial_mul_factorial kc]; ac_rfl
    _ ≤ _ := bound

private theorem cover_bound {n : Nat} (H : Finset (Perm (Fin n))) (a b : ↥H → Fin n → Bool)
    (priv : ∀ h,∃ p,∀ t,fits (a t) (b t) p ↔ t=h) :
    H.card ≤ max ((sample n).card-1) (n.choose (n/2)) := by
  classical
  let hits (h : ↥H) := univ.filter (fits (a h) (b h))
  by_cases over : ∃ p : Perm (Fin n),2≤(univ.filter (fun h => fits (a h) (b h) p)).card
  · obtain ⟨p,hp⟩ := over
    have small := rank_bound_overlap _ (avoids_detects n) H a b priv p hp
    exact le_trans (by omega : H.card≤(sample n).card-1) (le_max_left _ _)
  · have single (p : Perm (Fin n)) : (univ.filter (fun h => fits (a h) (b h) p)).card≤1 := by
      have h := not_exists.mp over p
      omega
    have slices (h : ↥H) : Fintype.card (Perm (Fin n)) ≤ (hits h).card * n.choose (n/2) := by
      obtain ⟨p,hp⟩ := priv h
      exact fraction (a h) (b h) p ((hp h).mpr rfl)
    have apart : ((univ : Finset (↥H)) : Set (↥H)).PairwiseDisjoint hits := by
      intro h _ k _ ne
      apply Finset.disjoint_left.mpr
      intro p hp kp
      apply ne
      exact card_le_one.mp (single p) _ (mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hp).2⟩)
        _ (mem_filter.mpr ⟨mem_univ _,(mem_filter.mp kp).2⟩)
    have total : ∑ h,(hits h).card ≤ Fintype.card (Perm (Fin n)) := by
      rw [←card_biUnion apart]
      exact card_le_univ _
    have h := calc
      H.card * Fintype.card (Perm (Fin n)) = ∑ _h : ↥H,Fintype.card (Perm (Fin n)) := by simp
      _ ≤ ∑ h,(hits h).card * n.choose (n/2) := sum_le_sum (fun h _ => slices h)
      _ ≤ Fintype.card (Perm (Fin n)) * n.choose (n/2) := by
        rw [←sum_mul]; exact Nat.mul_le_mul_right _ total
    rw [Nat.mul_comm (Fintype.card (Perm (Fin n)))] at h
    exact (Nat.le_of_mul_le_mul_right h Fintype.card_pos).trans (le_max_right _ _)

/-- Universal color-witness bound for reassigning a fixed set of points. -/
def paletteSize (n : Nat) := max ((sample n).card-1) (n.choose (n/2))

theorem slot_palette {V C : Type} (n : Nat) (E : C → V → V → Prop)
    (sym : ∀ c {x y},E c x y → E c y x) (u v : Fin n → V) :
    (∃ p : Perm (Fin n),passes E u v (assign p)) ↔
    ∀ S : Finset C,S.card≤paletteSize n → ∃ p : Perm (Fin n),
      ∀ c∈S,Connected (extend (E c) u v (assign p)) :=
  palette_from_covers _ (fun H a b _ => cover_bound H a b) E sym u v

theorem slot_palette_graph {n k : Nat} (d : Nat) (g : Coloring n k) (w : Lines n) (u v : Fin d → Fin n) :
    (∃ p : Perm (Fin d),Works g (draw w u v p)) ↔
    ∀ S : Finset (Fin k),S.card≤paletteSize d → ∃ p : Perm (Fin d),
      ∀ c∈S,Connected (Joined g (draw w u v p) c) := by
  simp_rw [show ∀ p c,Joined g (draw w u v p) c=extend (Joined g w c) u v (assign p) from
    fun p c => funext₂ (fun x y => propext (joined_draw g w u v p c x y))]
  simpa only [works_draw] using slot_palette d (Joined g w) (fun _ {_ _} h => joined_symm g h) u v

set_option maxRecDepth 20000 in
theorem first_bounds : paletteSize 1=1 ∧ paletteSize 2=2 ∧ paletteSize 3=4 ∧ paletteSize 4=13 := by decide

#print axioms slot_palette_graph
#print axioms first_bounds
end WildSlots
