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
#print axioms at_least_fourteen
end Fourteen
