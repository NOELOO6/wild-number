import PieceBudget
import PiecePaths
namespace WildPieces
open Finset WildCuts EdgeWalk WildDeletion

def half (t : Tags) (i : G) : Bool := decide (t i = t 0)

private theorem small_partition : ∀ t : Tags,
    (deficit t = 0 → ∀ i j, t i = t j) ∧
    (deficit t ≤ 1 → ∀ i j, half t i = half t j → t i = t j) := by
  native_decide

/-- Thirteen legal wild lines connect every color except possibly one. For the
exception its vertices can be put into two sets, with paths within each set. -/
theorem at_most_one_piece (g : WildLower.Coloring V) :
    ∃ (w : List (Edge 19)) (last : V), w.Nodup ∧ (∀ e ∈ w, e.1 < e.2) ∧ w.length = 13 ∧
      (∀ c, c ≠ last → Connected (Adj (w ++ g.edges c))) ∧
      ∃ f : V → Bool, ∀ x y, f x = f y → Walk (Adj (w ++ g.edges last)) x y := by
  classical
  obtain ⟨q,hq⟩ := Classical.axiomOfChoice (coordinates (k:=9) (by decide) (by decide +kernel)
    g.edges g.complete g.proper)
  obtain ⟨p,budget⟩ := choose_thirteen q
  let d := fun c => deficit (components (p*q c))
  change (∑ c, d c) ≤ 1 at budget
  have small (c : V) : d c ≤ 1 :=
    (Finset.single_le_sum (fun i _ => Nat.zero_le (d i)) (Finset.mem_univ c)).trans budget
  have exception : ∃ last : V, ∀ c, c ≠ last → d c = 0 := by
    by_cases bad : ∃ c, 0 < d c
    · obtain ⟨last,hl⟩ := bad
      refine ⟨last,fun c ne => ?_⟩
      have bound : (∑ i ∈ ({c,last} : Finset V), d i) ≤ ∑ i, d i :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      simp [ne] at bound
      omega
    · exact ⟨0,fun c _ => Nat.eq_zero_of_not_pos (fun h => bad ⟨c,h⟩)⟩
  obtain ⟨last,good⟩ := exception
  obtain ⟨unique,legal,count⟩ := stars_properties p.symm
  refine ⟨stars p.symm,last,unique,legal,count,?_,?_,?_⟩
  · intro c h x y
    exact actual_paths p _ _ (hq c) x y ((small_partition _).1 (good c h) _ _)
  · exact fun x => half (components (p*q last)) (groups19.tag (p x))
  · intro x y eq
    exact actual_paths p _ _ (hq last) x y ((small_partition _).2 (small last) _ _ eq)
#print axioms at_most_one_piece
end WildPieces
