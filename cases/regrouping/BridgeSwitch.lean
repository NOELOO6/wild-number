import TwoGroups
namespace WildExact.Regroup
open WildDeletion
namespace Switch

/-- Ends 0 and 1 form the first old edge, and 2 and 3 the second.
The exchange replaces them by 0--3 and 2--1. -/
def before (i : Fin 4) := decide (2≤i.val)
def after (i : Fin 4) := decide (i.val=1 ∨ i.val=2)

variable {V : Type} (E : V → V → Prop) (p : Fin 4 → V)
private theorem draw_sym (sym : ∀ {a b},E a b → E b a) (side : Fin 4 → Bool) :
    ∀ {a b},Draw E p side a b → Draw E p side b a := by
  rintro a b (h|⟨i,j,hi,hj,eq⟩)
  · exact Or.inl (sym h)
  · exact Or.inr ⟨j,i,hj,hi,eq.symm⟩

private theorem link (side : Fin 4 → Bool) (i j : Fin 4) (eq : side i=side j) :
    Walk (Draw E p side) (p i) (p j) := .step (.stay _) (Or.inr ⟨i,j,rfl,rfl,eq⟩)

private theorem flatten {side : Fin 4 → Bool} {a b : V} (h : Walk (Draw E p side) a b) :
    Walk (Draw E p (fun _ => false)) a b := by
  apply h.mapInto id
  rintro x y (e|⟨i,j,xi,yj,_⟩)
  · exact .step (.stay _) (Or.inl e)
  · exact .step (.stay _) (Or.inr ⟨i,j,xi,yj,rfl⟩)

private theorem merged (sym : ∀ {a b},E a b → E b a)
    (cover : ∀ v,Walk (Draw E p before) v (p 0) ∨ Walk (Draw E p before) v (p 2)) :
    Connected (Draw E p (fun _ => false)) := by
  have path (v) : Walk (Draw E p (fun _ => false)) v (p 0) := by
    rcases cover v with l|r
    · exact flatten E p l
    · exact (flatten E p r).join (link E p _ 2 0 rfl)
  exact fun a b => (path a).join (backwards (draw_sym E p sym _) (path b))

private theorem raw (side : Fin 4 → Bool)
    {a b : V} (h : Walk E a b) : Walk (Draw E p side) a b :=
  Walk.mapInto (E:=E) (F:=Draw E p side) id (fun _ _ e => .step (.stay _) (Or.inl e)) h

/-- In the two failed components, at least one removed edge must have an
alternative path between its own endpoints. This criterion is exact. -/
theorem two_parts (sym : ∀ {a b},E a b → E b a)
    (cover : ∀ v,Walk (Draw E p before) v (p 0) ∨ Walk (Draw E p before) v (p 2))
    (apart : ¬Walk (Draw E p before) (p 0) (p 2)) :
    Connected (Draw E p after) ↔ Walk E (p 0) (p 1) ∨ Walk E (p 2) (p 3) := by
  have both : ∃ i j,after i≠after j := ⟨0,1,by decide⟩
  rw [split_iff E p sym after both]
  constructor
  · rintro ⟨_,i,j,ne,h⟩
    have forbid (u v : Fin 4) (one : before u=false) (two : before v=true)
        (path : Walk E (p u) (p v)) : False :=
      apart (((link E p before 0 u (by simpa [before] using one.symm)).join (raw E p before path)).join
        (link E p before v 2 (by simpa [before] using two)))
    have eq : before i=before j := by
      cases a : before i <;> cases b : before j <;> try rfl
      · exact (forbid i j a b h).elim
      · exact (forbid j i b a (backwards sym h)).elim
    have cases4 : ∀ a b : Fin 4,before a=before b → after a≠after b →
        (a=0 ∧ b=1) ∨ (a=1 ∧ b=0) ∨ (a=2 ∧ b=3) ∨ (a=3 ∧ b=2) := by decide
    rcases cases4 i j eq ne with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact Or.inl h
    · exact Or.inl (backwards sym h)
    · exact Or.inr h
    · exact Or.inr (backwards sym h)
  · intro h
    refine ⟨merged E p sym cover,?_⟩
    rcases h with l|r
    · exact ⟨0,1,by decide,l⟩
    · exact ⟨2,3,by decide,r⟩

/-- For an already connected color, the switch survives exactly when one
of the four possible residual routes crosses the new pairing. -/
theorem keep_connected (sym : ∀ {a b},E a b → E b a) (old : Connected (Draw E p before)) :
    Connected (Draw E p after) ↔
      Walk E (p 0) (p 1) ∨ Walk E (p 0) (p 2) ∨ Walk E (p 3) (p 1) ∨ Walk E (p 3) (p 2) := by
  rw [split_iff E p sym after ⟨0,1,by decide⟩]
  constructor
  · rintro ⟨_,i,j,ne,h⟩
    have forward (a b : Fin 4) (a0 : after a=false) (b1 : after b=true) (path : Walk E (p a) (p b)) :
        Walk E (p 0) (p 1) ∨ Walk E (p 0) (p 2) ∨ Walk E (p 3) (p 1) ∨ Walk E (p 3) (p 2) := by
      have x : ∀ a,after a=false → a=0 ∨ a=3 := by decide
      have y : ∀ b,after b=true → b=1 ∨ b=2 := by decide
      rcases x a a0 with rfl|rfl <;> rcases y b b1 with rfl|rfl <;> tauto
    cases a : after i <;> cases b : after j <;> try exact (ne (a.trans b.symm)).elim
    · exact forward i j a b h
    · exact forward j i b a (backwards sym h)
  · intro paths
    refine ⟨fun x y => flatten E p (old x y),?_⟩
    rcases paths with h|h|h|h
    · exact ⟨0,1,by decide,h⟩
    · exact ⟨0,2,by decide,h⟩
    · exact ⟨3,1,by decide,h⟩
    · exact ⟨3,2,by decide,h⟩
end Switch
end WildExact.Regroup
