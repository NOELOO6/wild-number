import MatchingModel
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.EquivFin

namespace WildExact.RootedMatching
/-- Choose the endpoint at the distinguished root first, and otherwise the smaller endpoint. -/
def front {n} (r : Fin n) (f : Fin n → Fin n) (x : Fin n) : Prop :=
  x=r ∨ (f x≠r ∧ x<f x)
instance {n r f x} : Decidable (@front n r f x) := by unfold front; infer_instance

theorem other {n} {r : Fin n} {f : Fin n → Fin n} (inv : Function.Involutive f)
    (free : ∀ x, x ≠ f x) (x) : front r f (f x) ↔ ¬ front r f x := by
  unfold front
  rw [inv]
  by_cases a : x=r
  · subst x; simp [(free r).symm]
  by_cases b : f x=r
  · simp [a,b]
  · simp only [a,b,false_or,ne_eq,not_false_eq_true,true_and,not_lt]
    exact ⟨le_of_lt,fun h => lt_of_le_of_ne h (free x).symm⟩

abbrev Front {n} (r : Fin n) (f : Fin n → Fin n) := {x : Fin n // front r f x}

def point {n} {r : Fin n} (f : Fin n → Fin n) (p : Front r f × Bool) :=
  if p.2 then f p.1.1 else p.1.1

def frame {n} (r : Fin n) (f : Fin n → Fin n) (inv : Function.Involutive f) (free : ∀ x, x≠f x) :
    Front r f × Bool ≃ Fin n where
  toFun := point f
  invFun x := if h : front r f x then (⟨x,h⟩,false) else (⟨f x,(other inv free x).mpr h⟩,true)
  left_inv p := by
    obtain ⟨⟨x,h⟩,b⟩ := p
    cases b <;> simp [point,h,(other inv free x).not.mpr (not_not.mpr h),inv x]
  right_inv x := by by_cases h : front r f x <;> simp [point,h,inv x]

private theorem frame_flip {n} (r : Fin n) (f : Fin n → Fin n) (inv : Function.Involutive f)
    (free : ∀ x,x≠f x) (a : Front r f) (b : Bool) :
    frame r f inv free (a,!b) = f (frame r f inv free (a,b)) := by
  cases b <;> simp [frame,point,inv a.val]

/-- Two perfect matchings on the same finite vertex set can be identified by a
permutation fixing any designated root, with no assumption about their labels. -/
theorem conjugate {n} (r : Fin n) (f g : Fin n → Fin n)
    (fi : Function.Involutive f) (ff : ∀ x,x≠f x)
    (gi : Function.Involutive g) (gf : ∀ x,x≠g x) :
    ∃ q : Equiv.Perm (Fin n), q r = r ∧ ∀ x, q (f x)=g (q x) := by
  classical
  let F := frame r f fi ff
  let G := frame r g gi gf
  have a := Fintype.card_congr F
  have b := Fintype.card_congr G
  simp only [Fintype.card_prod,Fintype.card_bool,Fintype.card_fin] at a b
  let base : Front r f ≃ Front r g := Fintype.equivOfCardEq (by omega)
  let rf : Front r f := ⟨r,Or.inl rfl⟩
  let rg : Front r g := ⟨r,Or.inl rfl⟩
  let e := base.trans (Equiv.swap (base rf) rg)
  have er : e rf=rg := Equiv.swap_apply_left ..
  let q := F.symm.trans ((e.prodCongr (Equiv.refl Bool)).trans G)
  have eval (s : Front r f) (bit : Bool) : q (F (s,bit))=G (e s,bit) := by simp [q]
  refine ⟨q,?_,?_⟩
  · exact (show F (rf,false)=r from rfl) ▸ (eval rf false).trans (by rw [er]; rfl)
  intro x
  obtain ⟨⟨s,bit⟩,rfl⟩ := F.surjective x
  rw [← frame_flip r f fi ff s bit,eval,eval,frame_flip]

#print axioms conjugate
end WildExact.RootedMatching
