import CyclicScan
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.List.FinRange
import MatchingModel

namespace WildExact.Rotation
open WildExact EdgeWalk

variable {n : Nat}
local notation "V" => Fin (n+1)
local notation "Edges" => List (Edge (n+1))

/-- Coordinates for a full cycle permuting the color classes. Odd order makes
the missing colors canonical, so we need no separate permutation of colors. -/
def Cyclic (g : Coloring (n+1) (n+1)) (v : V ≃ V) := ∀ x y t : V, x≠y →
  g.paint (v x) (v y)=missingColor g (v 0) →
  g.paint (v (x+t)) (v (y+t))=missingColor g (v t)

private theorem extract (P : V → V → Prop) (test : Edges → Bool)
    (proper : ∀ x y z, P x y → P x z → y=z)
    (sym : ∀ x y, P x y → P y x) (ne : ∀ x y, P x y → x≠y)
    (distinct : ∀ a b x y, P a b → P x y → dist a b=dist x y → a=x ∨ a=y)
    (fuel : Nat) (xs : List V) (used : List Nat) (es : Edges)
    (size : xs.length≤2*fuel) (nodup : xs.Nodup)
    (paired : ∀ x∈xs, ∃ y∈xs, P x y)
    (fresh : ∀ x∈xs, ∀ y∈xs, P x y → dist x y∉used)
    (prev : ∀ e∈es, P e.1 e.2) (ok : scan test fuel xs used es=true) :
    ∃ s, test s=true ∧ ∀ e∈s, P e.1 e.2 := by
  induction fuel generalizing xs used es with
  | zero =>
    have empty : xs=[] := List.length_eq_zero_iff.mp (by omega)
    subst xs
    exact ⟨es,ok,prev⟩
  | succ fuel ih =>
    cases xs with
    | nil => exact ⟨es,ok,prev⟩
    | cons a rest =>
      obtain ⟨b,hb,ab⟩ := paired a (by simp)
      have br : b∈rest := (List.mem_cons.mp hb).resolve_left (ne a b ab).symm
      have au := (List.nodup_cons.mp nodup).1
      have d := fresh a (by simp) b hb ab
      have next := List.all_eq_true.mp ok b br
      simp only [decide_eq_false d, Bool.false_or] at next
      let ys := rest.erase b
      have back {z : V} (h : z∈ys) : z∈rest := List.mem_of_mem_erase h
      have nb : b∉ys := (List.nodup_cons.mp nodup).2.not_mem_erase
      have toYs {z : V} (zr : z∈rest) (diff : z≠b) : z∈ys :=
        (List.mem_erase_of_ne diff).mpr zr
      apply ih ys (dist a b :: used) ((a,b)::es) _ ((List.nodup_cons.mp nodup).2.erase _) _ _ _ next
      · dsimp [ys]
        rw [List.length_erase_of_mem br]
        simp only [List.length_cons] at size
        omega
      · intro x hx
        obtain ⟨y,hy,xy⟩ := paired x (List.mem_cons_of_mem _ (back hx))
        have xa : x≠a := fun e => au (e ▸ back hx)
        have xb : x≠b := fun e => nb (e ▸ hx)
        have ya : y≠a := by
          rintro rfl
          exact xb (proper y x b (sym _ _ xy) ab)
        have yb : y≠b := by
          rintro rfl
          exact xa (proper y x a (sym _ _ xy) (sym _ _ ab))
        exact ⟨y,toYs ((List.mem_cons.mp hy).resolve_left ya) yb,xy⟩
      · intro x hx y hy xy hd
        rcases List.mem_cons.mp hd with eq|old
        · rcases distinct a b x y ab xy eq.symm with e|e
          · exact au (e ▸ back hx)
          · exact au (e ▸ back hy)
        · exact fresh x (List.mem_cons_of_mem _ (back hx)) y (List.mem_cons_of_mem _ (back hy)) xy old
      · intro e he
        rcases List.mem_cons.mp he with rfl|h
        · exact ab
        · exact prev e h

private theorem translate_pair (a b x y : V) (d : dist a b=dist x y) :
    (a+(x-a)=x ∧ b+(x-a)=y) ∨ (a+(y-a)=y ∧ b+(y-a)=x) := by
  have value (u v : V) : (u-v).val = if v.val≤u.val then u.val-v.val else n+1+u.val-v.val := by
    split
    · exact Fin.sub_val_of_le ‹_›
    · exact Fin.coe_sub_iff_lt.mpr (by omega)
  have eq : (b-a).val=(y-x).val ∨ (b-a).val=(x-y).val := by
    unfold dist at d
    rw [value,value,value]
    split_ifs <;> omega
  have move (u z : V) (h : b-a=z-u) : a+(u-a)=u ∧ b+(u-a)=z := by
    constructor
    · rw [add_comm a (u-a),sub_add_cancel]
    · calc
        b+(u-a) = (b-a)+u := by simp only [sub_eq_add_neg]; ac_rfl
        _ = z := by rw [h,sub_add_cancel]
  exact eq.elim (fun h => Or.inl (move _ _ (Fin.ext h))) (fun h => Or.inr (move _ _ (Fin.ext h)))


/-- In any odd order, the edges of the color missing at zero occur in the
exhaustive search. Unique circular lengths follow from color equivariance. -/
theorem find_starter (odd : (n+1)%2=1) (g : Coloring (n+1) (n+1)) (v : V ≃ V) (rot : Cyclic g v)
    (test : Edges → Bool) (checked : scan test (n/2) (List.finRange (n+1)).tail [] []=true) :
    ∃ s, test s=true ∧ ∀ e∈s, e.1≠e.2 ∧ g.paint (v e.1) (v e.2)=missingColor g (v 0) := by
  let P (x y : V) := x≠y ∧ g.paint (v x) (v y)=missingColor g (v 0)
  have inj := missing_injective odd g
  have uniq (x y z) (xy : P x y) (xz : P x z) : y=z :=
    v.injective (g.proper _ _ _ (fun e => xy.1 (v.injective e))
      (fun e => xz.1 (v.injective e)) (xy.2.trans xz.2.symm))
  have sym (x y) (xy : P x y) : P y x := ⟨xy.1.symm,(g.symm _ _).trans xy.2⟩
  have tail (x : V) : x∈(List.finRange (n+1)).tail ↔ x≠0 := by
    rw [List.finRange_succ]
    simp [Fin.exists_succ_eq]
  apply extract P test uniq sym (fun _ _ h => h.1) _ (n/2) (List.finRange (n+1)).tail [] [] (by simp; omega)
    ((List.nodup_finRange _).tail) _ (by simp) (by simp) checked
  · intro a b x y ab xy d
    have one (u z t : V) (au : a+t=u) (bz : b+t=z) (uz : P u z) : a=u := by
      have c := rot a b t ab.1 ab.2
      rw [au,bz,uz.2] at c
      have eq := v.injective (inj c.symm)
      simpa [eq] using au
    rcases translate_pair a b x y d with h|h
    · exact Or.inl (one x y _ h.1 h.2 xy)
    · exact Or.inr (one y x _ h.1 h.2 (sym x y xy))
  · intro x hx
    have non : ¬Absent g (v x) (missingColor g (v 0)) := by
      intro h
      have eq := (unique_missing g (v x)).choose_spec.2 _ h
      exact (tail x).mp hx (v.injective (inj eq.symm))
    unfold Absent at non
    push_neg at non
    obtain ⟨u,xu,col⟩ := non
    have nz : v.symm u≠0 := by
      intro z
      have u0 : u=v 0 := by simpa using congrArg v z
      subst u
      exact absent_missing g (v 0) _ xu.symm ((g.symm _ _).trans col)
    exact ⟨v.symm u,(tail _).mpr nz,by simpa [P] using
      (show x≠v.symm u ∧ g.paint (v x) u=missingColor g (v 0) from
        ⟨fun e => xu (by simpa using congrArg v e),col⟩)⟩

end WildExact.Rotation
