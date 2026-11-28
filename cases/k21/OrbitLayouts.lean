import ExactModel

namespace WildExact
open WildDeletion

/-- A path certificate may be checked on a different vertex type, using one
test graph for each orbit of colors. -/
theorem works_of_walk_cover {n k : Nat} {g : Coloring n k} {w : Lines n}
    {A I : Type} (R : I → A → A → Prop) (good : ∀ i, Connected (R i))
    (cover : ∀ c, ∃ (i : I) (p : A → Fin n), Function.Surjective p ∧
      ∀ x y, R i x y → Joined g w c (p x) (p y)) : Works g w := by
  intro c x y
  obtain ⟨i,p,onto,maps⟩ := cover c
  obtain ⟨a,rfl⟩ := onto x
  obtain ⟨b,rfl⟩ := onto y
  exact Walk.mapInto p (fun u v e => .step (.stay _) (maps u v e)) (good i a b)

end WildExact
