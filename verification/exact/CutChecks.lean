import CutValidation
import Counting
namespace WildExact.Seventeen
set_option maxRecDepth 10000

private theorem checked : validateCuts=true := by native_decide

theorem key_facts :
  (∀ p : Small, ∀ k ∈ localCuts p, k∈allKeys) ∧
  (∀ k∈allKeys, k<16384 ∧ ∀ p : Small, (partFlags k).testBit p.val = (localCuts p).contains k) ∧
  (∀ (b : Big) (k : Nat), k∈allKeys → embed b k < 262144) := by
  have all := checked
  unfold validateCuts at all
  simp only [Bool.and_eq_true] at all
  obtain ⟨⟨localRange,flags⟩,bounds⟩ := all
  refine ⟨fun p k hk => List.contains_iff_mem.mp (List.all_eq_true.mp
    (List.all_eq_true.mp localRange p (List.mem_finRange _)) k hk),?_,?_⟩
  · intro k hk
    obtain ⟨bound,yes⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp flags k hk)
    exact ⟨of_decide_eq_true bound,fun p => eq_of_beq (List.all_eq_true.mp yes _ (List.mem_finRange p))⟩
  · intro b k hk
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp bounds _ (List.mem_finRange b)) k hk)

end WildExact.Seventeen
