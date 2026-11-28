import MomentPairs36
import PatternGeometry

namespace WildSieve.ThirtySix
open Finset
local instance (priority := 2000) geometryVertexEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq
export SixCounts (two_from wedge_view wedge_size through_le event event_union event_empty event_pattern_union)

theorem event_mass {P : Pattern} (ok : Triples P) : (event P).card=ways (12-P.card) :=
  SixCounts.event_mass 12 (by decide) ok

/-- Relative positions used to count a third compatible two-block pattern. -/
def Detached (P Q R : Pattern) := Separate (P∪Q) R
def JoinsLeaf (P Q R : Pattern) := ∃ A∈P \ Q,A∈R
def JoinsCenter (P Q R : Pattern) := ∃ A∈P∩Q,A∈R
def ClosesTriangle (P Q R : Pattern) := R=(P \ Q)∪(Q \ P)

noncomputable def charge (p : Prop) (n : Nat) : Nat := by classical exact if p then n else 0

@[simp] theorem charge_yes {p : Prop} (h : p) (v : Nat) : charge p v=v := by simp [charge,h]
@[simp] theorem charge_no {p : Prop} (h : ¬p) (v : Nat) : charge p v=0 := by simp [charge,h]

/-- The symmetric part counts three separate edges, a star, or a triangle.
The oriented part singles out the center of a path or the isolated edge. -/
noncomputable def symmetricCost (P Q R : Pattern) :=
  charge (Separate P Q ∧ Detached P Q R) (ways 6)+
  charge (Wedge P Q ∧ JoinsCenter P Q R) (ways 8)+
  charge (Wedge P Q ∧ ClosesTriangle P Q R) (ways 9)
noncomputable def orientedCost (P Q R : Pattern) :=
  charge (Wedge P Q ∧ Detached P Q R) (ways 7)+
  charge (Wedge P Q ∧ JoinsLeaf P Q R) (ways 8)

end WildSieve.ThirtySix
