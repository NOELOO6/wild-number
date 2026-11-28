import CyclicPrune
import CyclicExtraction
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Fintype.Prod

namespace WildExact.Rotation
open EdgeWalk Finset
variable {n : Nat}
local notation "V" => Fin (n+1)
local notation "Edges" => List (Edge (n+1))

private def relaxed (allow : V → V → Bool) (test : Edges → Bool) (s : Edges) :=
  !s.all (fun e => allow e.1 e.2) || test s

private theorem scan_relaxed (allow : V → V → Bool) (test : Edges → Bool)
    (fuel : Nat) (xs : List V) (used : List Nat) (es : Edges) (sz : xs.length≤2*fuel)
    (ok : es.all (fun e => allow e.1 e.2)=false ∨ scanAllowed allow test fuel xs used es=true) :
    scan (relaxed allow test) fuel xs used es=true := by
  induction fuel generalizing xs used es with
  | zero =>
    have eq : xs=[] := List.length_eq_zero_iff.mp (by omega)
    subst xs; rcases ok with no|yes
    · simp [scan,relaxed,no]
    · simp only [scanAllowed] at yes; simp [scan,relaxed,yes]
  | succ k ih =>
    cases xs with
    | nil =>
      rcases ok with no|yes
      · simp [scan,relaxed,no]
      · simp only [scanAllowed] at yes; simp [scan,relaxed,yes]
    | cons a rest =>
      apply List.all_eq_true.mpr
      intro b hb
      by_cases usedB : dist a b∈used
      · simp [usedB]
      · simp only [decide_eq_false usedB,Bool.false_or]
        apply ih
        · rw [List.length_erase_of_mem hb]; simp only [List.length_cons] at sz; omega
        rcases ok with no|yes
        · exact Or.inl (by simp [List.all_cons,no])
        by_cases bad : allow a b=false
        · exact Or.inl (by simp [bad])
        · have chk := List.all_eq_true.mp yes b hb
          exact Or.inr (by simpa [bad,usedB] using chk)

/-- Reindex by multiplication with an invertible residue. -/
def scalar (u a : V) (inv : u*a=1) : V ≃ V where
  toFun x := u*x
  invFun y := a*y
  left_inv x := by simp only [←mul_assoc,mul_comm a u,inv,one_mul]
  right_inv x := by simp only [←mul_assoc,inv,one_mul]

theorem scalar_cyclic {g : Coloring (n+1) (n+1)} {v : V ≃ V} (rot : Cyclic g v)
    (u a : V) (inv : u*a=1) : Cyclic g ((scalar u a inv).symm.trans v) := by
  intro x y t xy h
  change g.paint (v (a*x)) (v (a*y))=missingColor g (v (a*0)) at h
  rw [mul_zero] at h
  have ne := (scalar u a inv).symm.injective.ne xy
  change g.paint (v (a*(x+t))) (v (a*(y+t)))=missingColor g (v (a*t))
  rw [mul_add,mul_add]
  exact rot (a*x) (a*y) (a*t) ne h

/-- Normalize the partner of 1 in the color missing at zero. Some cyclic
labeling minimizes this partner over all cyclic labelings. Multiplying
the endpoints of any starter edge by a unit therefore cannot give a
smaller partner of 1. -/
theorem normalized_coordinates (g : Coloring (n+1) (n+1)) (v : V ≃ V)
    (odd : (n+1)%2=1) (one : (1 : V)≠0) (rot : Cyclic g v) :
    ∃ w : V ≃ V, Cyclic g w ∧ ∃ t : V,
      ∀ x y : V,x≠y → g.paint (w x) (w y)=missingColor g (w 0) →
        (x=1 → y=t) ∧ (∀ u : V,u*x=1 → t.val≤(u*y).val) ∧
          (∀ u : V,u*y=1 → t.val≤(u*x).val) := by
  classical
  let P (w : V ≃ V) (x y : V) := x≠y ∧ g.paint (w x) (w y)=missingColor g (w 0)
  let good := (univ : Finset ((V ≃ V) × V)).filter fun z => Cyclic g z.1 ∧ P z.1 1 z.2
  have existsPartner : ∃ t : V,P v 1 t := by
    have h : ¬Absent g (v 1) (missingColor g (v 0)) := by
      intro z
      exact one (v.injective (missing_injective odd g ((unique_missing g (v 1)).choose_spec.2 _ z).symm))
    unfold Absent at h
    push_neg at h
    obtain ⟨z,ne,col⟩ := h
    exact ⟨v.symm z,fun e => ne (by simpa using congrArg v e),by simpa using col⟩
  obtain ⟨t₀,ht⟩ := existsPartner
  obtain ⟨⟨w,t⟩,hw,small⟩ := exists_min_image good (fun z => z.2.val)
    ⟨(v,t₀),mem_filter.mpr ⟨mem_univ _,rot,ht⟩⟩
  obtain ⟨cyc,wt⟩ := (mem_filter.mp hw).2
  refine ⟨w,cyc,t,fun x y xy col => ?_⟩
  have minimum (a b u : V) (h : P w a b) (inv : u*a=1) : t.val≤(u*b).val := by
    let e := scalar u a inv
    let z := e.symm.trans w
    have ea : e.symm 1=a := by change a*1=a; simp
    have eb : e.symm (u*b)=b := e.symm_apply_apply b
    have zero : e.symm 0=0 := by change a*0=0; simp
    apply small (z,u*b) (mem_filter.mpr ⟨mem_univ _,scalar_cyclic cyc u a inv,?_,?_⟩)
    · exact fun eq => h.1 (ea ▸ eb ▸ congrArg e.symm eq)
    · change g.paint (w (e.symm 1)) (w (e.symm (u*b)))=missingColor g (w (e.symm 0))
      simpa only [ea,eb,zero] using h.2
  refine ⟨?_,fun u => minimum x y u ⟨xy,col⟩,fun u => minimum y x u ⟨xy.symm,(g.symm _ _).trans col⟩⟩
  rintro rfl
  exact w.injective (g.proper _ _ _ (w.injective.ne xy) (w.injective.ne wt.1) (col.trans wt.2.symm))

theorem find_allowed_starter (g : Coloring (n+1) (n+1)) (v : V ≃ V) (odd : (n+1)%2=1)
    (rot : Cyclic g v) (allow : V → V → Bool) (test : Edges → Bool)
    (valid : ∀ a b,a≠b → g.paint (v a) (v b)=missingColor g (v 0) → allow a b=true)
    (checked : scanAllowed allow test (n/2) (List.finRange (n+1)).tail [] []=true) :
    ∃ s,test s=true ∧ ∀ e∈s,e.1≠e.2 ∧ g.paint (v e.1) (v e.2)=missingColor g (v 0) := by
  have sz : (List.finRange (n+1)).tail.length≤2*(n/2) := by simp; omega
  obtain ⟨s,ok,edges⟩ := find_starter odd g v rot (relaxed allow test)
    (scan_relaxed allow test _ _ _ _ sz (Or.inr checked))
  have all : s.all (fun e => allow e.1 e.2)=true := List.all_eq_true.mpr (fun e he => valid _ _ (edges _ he).1 (edges _ he).2)
  exact ⟨s,by simpa [relaxed,all] using ok,edges⟩
end WildExact.Rotation
