import PairFrames
namespace WildExact.Seventeen
open WildExact

private theorem checked_pairs : allSecond=true := by native_decide

/-- Every ordered pair of distinct colors in any proper K17 coloring has one
of the fifteen certificate forms after adjoining the missing-color root. -/
theorem colors_normalize (g : Coloring 17 17) (c d : Fin 17) (ne : c≠d) :
    ∃ (i : Fin 15) (q : Equiv.Perm V), q root=root ∧
      (∀ x, q (entry (canon i).1 x) = mate (augment (by decide) g) c (q x)) ∧
      ∀ x, q (entry (canon i).2 x) = mate (augment (by decide) g) d (q x) := by
  let h := augment (by decide) g
  apply pair_normalization _ _ (mate_involutive h c) (fun x => (mate_spec h c x).1)
    (mate_involutive h d) (fun x => (mate_spec h d x).1) _ checked_pairs
  intro x eq
  have left := (mate_spec h c x).2
  have right := (mate_spec h d x).2
  rw [eq] at left
  exact ne (left.symm.trans right)

#print axioms colors_normalize
end WildExact.Seventeen
