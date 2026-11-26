import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import EdgeWalk

namespace WildExact
open Finset WildDeletion
/-- Proper coloring of the ordinary edges of the complete graph. The diagonal
of the table is ignored. Odd n uses n colors and even n uses n-1. -/
structure Coloring (n k : Nat) where
  paint : Fin n → Fin n → Fin k
  symm : ∀ x y, paint x y = paint y x
  proper : ∀ x y z, x ≠ y → x ≠ z → paint x y = paint x z → y = z

abbrev Lines (n : Nat) := Finset (Fin n × Fin n)
def Legal {n} (w : Lines n) := ∀ e ∈ w, e.1 < e.2
def Touch {n} (w : Lines n) (x y : Fin n) := (x,y) ∈ w ∨ (y,x) ∈ w
def Joined {n k} (g : Coloring n k) (w : Lines n) (c : Fin k) (x y : Fin n) :=
  Touch w x y ∨ (x ≠ y ∧ g.paint x y = c)
def Works {n k} (g : Coloring n k) (w : Lines n) := ∀ c, Connected (Joined g w c)
def Upper {n k} (g : Coloring n k) (b : Nat) := ∃ w, Legal w ∧ w.card ≤ b ∧ Works g w
def Exact {n k} (g : Coloring n k) (b : Nat) :=
  (∃ w, Legal w ∧ w.card = b ∧ Works g w) ∧ ∀ w, Legal w → Works g w → b ≤ w.card

theorem joined_symm {n k} (g : Coloring n k) {w c x y} :
    Joined g w c x y → Joined g w c y x := by
  rintro ((h|h)|⟨h,col⟩)
  · exact Or.inl (Or.inr h)
  · exact Or.inl (Or.inl h)
  · exact Or.inr ⟨h.symm,(g.symm y x).trans col⟩

theorem backwards {V : Type} {R : V → V → Prop} (sym : ∀ {x y}, R x y → R y x)
    {x y} (h : Walk R x y) : Walk R y x := by
  induction h with
  | stay => exact .stay _
  | step _ e ih => exact (Walk.step (.stay _) (sym e)).join ih

def restrict {n k} (g : Coloring (n+1) k) : Coloring n k where
  paint x y := g.paint x.castSucc y.castSucc
  symm _ _ := g.symm _ _
  proper _ _ _ hxy hxz h := Fin.castSucc_injective _ (g.proper _ _ _
    (fun e => hxy (Fin.castSucc_injective _ e)) (fun e => hxz (Fin.castSucc_injective _ e)) h)

def liftLine {n} : (Fin n × Fin n) ↪ (Fin (n+1) × Fin (n+1)) :=
  (Fin.castLEEmb (Nat.le_succ n)).prodMap (Fin.castLEEmb (Nat.le_succ n))

theorem even_upper {n b} (oddUpper : ∀ g : Coloring n n, Upper g b)
    (g : Coloring (n+1) n) : Upper g b := by
  obtain ⟨w,legal,size,paths⟩ := oddUpper (restrict g)
  refine ⟨w.map liftLine, ?_, (Finset.card_map _).le.trans size, ?_⟩
  · intro e he
    obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp he
    exact legal a ha
  intro c
  have reach (x y : Fin n) : Walk (Joined g (w.map liftLine) c) x.castSucc y.castSucc := by
    apply Walk.mapInto Fin.castSucc _ (paths c x y)
    intro a b h
    apply Walk.step (.stay _)
    rcases h with (h|h)|⟨ne,eq⟩
    · exact Or.inl (Or.inl (Finset.mem_map.mpr ⟨_,h,rfl⟩))
    · exact Or.inl (Or.inr (Finset.mem_map.mpr ⟨_,h,rfl⟩))
    · exact Or.inr ⟨fun e => ne (Fin.castSucc_injective _ e), eq⟩
  let endColor := fun v : Fin n => g.paint (Fin.last n) v.castSucc
  have inj : Function.Injective endColor := by
    intro a b h
    exact Fin.castSucc_injective _ (g.proper _ _ _ (Fin.ne_of_gt (Fin.castSucc_lt_last _))
      (Fin.ne_of_gt (Fin.castSucc_lt_last _)) h)
  obtain ⟨v,hv⟩ := (Finite.injective_iff_surjective.mp inj) c
  have edge : Joined g (w.map liftLine) c (Fin.last n) v.castSucc :=
    Or.inr ⟨Fin.ne_of_gt (Fin.castSucc_lt_last _),hv⟩
  have all (x : Fin (n+1)) : Walk (Joined g (w.map liftLine) c) v.castSucc x :=
    Fin.lastCases (Walk.step (.stay _) (joined_symm g edge)) (fun i => reach v i) x
  intro x y
  exact (backwards (joined_symm g) (all x)).join (all y)
end WildExact
