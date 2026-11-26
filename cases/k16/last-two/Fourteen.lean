import Bounds
namespace Fourteen
open Finset
/-- If the groupings for any two omitted colors cover 8,527 possibilities,
at most one of the fifteen individual choices has fewer than 4,264. -/
theorem at_least_fourteen (count : Fin 15 → Nat)
    (pair : ∀ a b, a ≠ b → 8527 ≤ count a + count b) :
    14 ≤ (univ.filter fun a => 4264 ≤ count a).card := by
  let bad := univ.filter (fun a => count a < 4264)
  have small : bad.card ≤ 1 := by
    by_contra! h
    obtain ⟨a,ha,b,hb,ne⟩ := Finset.one_lt_card.mp h
    have h₁ := (Finset.mem_filter.mp ha).2
    have h₂ := (Finset.mem_filter.mp hb).2
    have hp := pair a b ne
    omega
  have eq : (univ.filter fun a => 4264 ≤ count a) = badᶜ := by ext; simp [bad]
  rw [eq,Finset.card_compl]
  have size : Fintype.card (Fin 15) = 15 := rfl
  omega

/-- Here A and B are the winning layouts for the respective fourteen-color
sets. Their union contains every layout that keeps the shared thirteen colors
and at least one of the outside pair. -/
theorem count_pair {L : Type} [DecidableEq L] (a b : Finset L)
    (cover : 8527 ≤ (a∪b).card) : 8527 ≤ a.card + b.card :=
  le_trans cover (Finset.card_union_le a b)
/-- Add the inequalities for fifteen neighboring pairs in a cyclic ordering
of the colors. Each individual count is charged exactly twice. -/
theorem total_fourteen (count : Fin 15 → Nat)
    (pair : ∀ a b, a ≠ b → 8527 ≤ count a + count b) : 63953 ≤ ∑ a, count a := by
  let shift : Equiv.Perm (Fin 15) := {
    toFun := fun a => ⟨(a.val+1)%15,by omega⟩
    invFun := fun a => ⟨(a.val+14)%15,by omega⟩
    left_inv := by decide
    right_inv := by decide }
  have different : ∀ a : Fin 15, a ≠ shift a := by decide
  have cycle : (∑ a, count (shift a)) = ∑ a, count a :=
    Fintype.sum_equiv shift (fun a => count (shift a)) count (fun _ => rfl)
  have h := Finset.sum_le_sum (s:=univ) (fun a _ => pair a (shift a) (different a))
  rw [Finset.sum_add_distrib,cycle] at h
  have size : (∑ _ : Fin 15, (8527 : Nat)) = 127905 := by decide
  omega
#print axioms total_fourteen
#print axioms at_least_fourteen
end Fourteen
