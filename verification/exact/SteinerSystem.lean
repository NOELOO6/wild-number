import MatchingModel

namespace WildSteiner
open WildExact

/-- The third point of a Steiner triple system, with the diagonal filled
by the point itself. -/
structure System (A : Type) where
  third : A → A → A
  same : ∀ x,third x x=x
  swap : ∀ x y,third x y=third y x
  again : ∀ x y,third x (third x y)=y

namespace System
variable {A : Type} (S : System A)

theorem left_ne {x y : A} (h : x≠y) : S.third x y≠x := by
  intro eq
  have p := S.again x y
  rw [eq,S.same] at p
  exact h p

theorem right_ne {x y : A} (h : x≠y) : S.third x y≠y := (S.swap x y) ▸ S.left_ne h.symm

theorem recover (x y : A) : S.third y (S.third x y)=x := by rw [S.swap x y,S.again]

def reindex {B : Type} (w : B ≃ A) : System B where
  third x y := w.symm (S.third (w x) (w y))
  same x := by simp [S.same]
  swap x y := congrArg w.symm (S.swap _ _)
  again x y := by simp [S.again]

end System

/-- The color of each ordinary edge is the color missing at the third
point of its Steiner line. Point and color labels may be arbitrary. -/
def SteinerColoring {n : Nat} (g : Coloring n n) := ∃ S : System (Fin n),
  ∀ x y : Fin n,x≠y → g.paint x y=missingColor g (S.third x y)

end WildSteiner
