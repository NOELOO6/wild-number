import Std

/- Reachability under adding or deleting a point that has exactly one
   neighbour in the graph of one color plus the chosen wild edges. -/
namespace WildDeletion

inductive Walk {V : Type} (E : V → V → Prop) : V → V → Prop where
  | stay (v : V) : Walk E v v
  | step {a b c : V} : Walk E a b → E b c → Walk E a c

def Connected {V : Type} (E : V → V → Prop) := ∀ a b, Walk E a b

theorem Walk.join {V : Type} {E : V → V → Prop} {a b c : V}
    (h : Walk E a b) (g : Walk E b c) : Walk E a c := by
  induction g with
  | stay => exact h
  | step _ e ih => exact .step ih e

theorem Walk.mapInto {V U : Type} {E : V → V → Prop} {F : U → U → Prop}
    (f : V → U) (preserves : ∀ a b, E a b → Walk F (f a) (f b))
    {a b} (h : Walk E a b) : Walk F (f a) (f b) := by
  induction h with
  | stay => exact .stay _
  | step _ e ih => exact ih.join (preserves _ _ e)

/-- The additional point is none. Its unique neighbour has been named p. -/
def withLeaf {V : Type} (E : V → V → Prop) (p : V) : Option V → Option V → Prop
  | none, none => False
  | none, some b => b = p
  | some a, none => a = p
  | some a, some b => E a b

theorem leaf_iff {V : Type} (E : V → V → Prop) (p : V) :
    Connected (withLeaf E p) ↔ Connected E := by
  constructor
  · intro big a b
    let shrink : Option V → V := fun x => x.getD p
    have maps : ∀ x y, withLeaf E p x y → Walk E (shrink x) (shrink y) := by
      intro x y edge
      cases x with
      | none =>
        cases y with
        | none => exact False.elim edge
        | some y =>
          have eq : y = p := edge
          subst y
          exact .stay _
      | some x =>
        cases y with
        | none =>
          have eq : x = p := edge
          subst x
          exact .stay _
        | some y => exact .step (.stay _) edge
    exact Walk.mapInto shrink maps (big (some a) (some b))
  · intro small a b
    have old (x y : V) : Walk (withLeaf E p) (some x) (some y) :=
      Walk.mapInto some (fun _ _ h => .step (.stay _) h) (small x y)
    have enter : Walk (withLeaf E p) none (some p) := .step (.stay _) rfl
    have leave' : Walk (withLeaf E p) (some p) none := .step (.stay _) rfl
    cases a with
    | none =>
      cases b with
      | none => exact .stay _
      | some y => exact enter.join (old p y)
    | some x =>
      cases b with
      | none => exact (old x p).join leave'
      | some y => exact old x y

/-- The same wild relation is used for every color. -/
theorem same_wild_edges_iff {V C : Type} (color : C → V → V → Prop)
    (wild : V → V → Prop) (partner : C → V) :
    (∀ c, Connected (withLeaf (fun a b => color c a b ∨ wild a b) (partner c))) ↔
    (∀ c, Connected (fun a b => color c a b ∨ wild a b)) := by
  constructor <;> intro h c
  · exact (leaf_iff _ _).mp (h c)
  · exact (leaf_iff _ _).mpr (h c)

#print axioms same_wild_edges_iff
end WildDeletion
