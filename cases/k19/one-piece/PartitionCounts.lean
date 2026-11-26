import GroupMerges
namespace WildPieces
open Finset
set_option maxRecDepth 20000
set_option maxHeartbeats 0

def firsts {k} (a : G → Fin k) (v : Fin k) := ((List.finRange 6).map a).idxOf v
def patterns (k : Nat) := (univ : Finset (G → Fin k)).filter fun a =>
  (∀ i, firsts a i < 6) ∧ ∀ i j, i < j → firsts a i < firsts a j
def waysSplit (k : Nat) (t : Tags) := ∑ a ∈ patterns k, if coarse t a then 1 else 0
def total (k : Nat) := ∑ a ∈ patterns k, mass a

def normalize (t : Tags) (i : G) := ((List.finRange 6).find? (fun j => t i == t j)).getD i

private theorem norm_facts : ∀ t : Tags, normalize (normalize t) = normalize t ∧
    deficit (normalize t) = deficit t ∧ ∀ i j, normalize t i = normalize t j ↔ t i = t j := by
  native_decide

private theorem same_splits (t : Tags) (k : Nat) : waysSplit k (normalize t) = waysSplit k t := by
  apply Finset.sum_congr rfl
  intro a _
  have eq : coarse (normalize t) a ↔ coarse t a :=
    ⟨fun h i j e => h i j (((norm_facts t).2.2 _ _).mpr e),fun h i j e => h i j (((norm_facts t).2.2 _ _).mp e)⟩
  by_cases h : coarse t a <;> simp [eq,h]

-- The six groups have 203 possible component partitions. Only canonical label
-- functions reach the inner test, so this checks all 203 small cases.
private theorem canonical_bound : ∀ t : Tags, normalize t = t →
    deficit t + waysSplit 3 t ≤ waysSplit 2 t + 2*waysSplit 4 t := by native_decide

theorem split_bound (t : Tags) : deficit t + waysSplit 3 t ≤ waysSplit 2 t + 2*waysSplit 4 t := by
  simpa only [(norm_facts t).2.1,same_splits] using canonical_bound (normalize t) (norm_facts t).1

theorem sum_splits (k : Nat) :
    (∑ p : Equiv.Perm V, waysSplit k (components p)) = total k := by
  unfold waysSplit total
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  trans ∑ p : Equiv.Perm V, if compatible a p then 1 else 0
  · apply Finset.sum_congr rfl
    intro p _
    by_cases h : compatible a p <;> simp [coarse_components,h]
  · exact mass_correct a
end WildPieces
