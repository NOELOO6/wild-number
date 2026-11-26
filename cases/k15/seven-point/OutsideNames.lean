import InsideNames
import CertifiedRedraw
namespace InsideNames
open RedrawModel VertexRedraw EdgeWalk WildDeletion
open SixBoundary (ref)

def missing (x : V) : C := (colors.find? (fun c => ref c 15 == x)).getD 0

def OutsideFixed := ∀ (f : C→V→V), (∀ c x, f c (f c x)=x) → (∀ c x, f c x≠x) →
    (∀ c d,c≠d → ∀ x,f c x≠f d x) → (∀ x y : V,x≠y → ∃ c,f c x=y) →
    (∀ c x,6≤x.val → 6≤(ref c x).val → f c x=ref c x) → Wins f

/-- Renumber the six inside points by their missing colors. This preserves
the set of groupings and lets the six inside missing colors change freely. -/
theorem outside_names (known : AllRedraws) : OutsideFixed := by
  classical
  intro f inv ne proper cover agree
  have rc : ∀ c : C, missing (ref c 15)=c := by native_decide
  have rv : ∀ x : V, x≠15 → ref (missing x) 15=x := by native_decide
  have ri : ∀ c x, ref c (ref c x)=x := by native_decide
  have rn : ∀ c, ref c 15≠15 := by native_decide
  let actual (x : V) : C := if h : (15:V)≠x then Classical.choose (cover 15 x h) else 0
  have value {x : V} (hx : x≠15) : f (actual x) 15=x := by
    simp only [actual,dif_pos (Ne.symm hx)]
    exact Classical.choose_spec (cover 15 x (Ne.symm hx))
  have owner (c : C) : actual (f c 15)=c := by
    apply Classical.byContradiction
    intro h
    exact proper _ _ h 15 (value (ne c 15))
  let P (x : V) := if x=15 then 15 else f (missing x) 15
  let Q (x : V) := if x=15 then 15 else ref (actual x) 15
  have pf (c) : P (ref c 15)=f c 15 := by simp [P,rn c,rc]
  have qf (c) : Q (f c 15)=ref c 15 := by simp [Q,ne c 15,owner]
  have qp (x : V) : Q (P x)=x := by
    by_cases h : x=15
    · simp [P,Q,h]
    · rw [show P x=f (missing x) 15 by simp [P,h],qf,rv x h]
  have pq (x : V) : P (Q x)=x := by
    by_cases h : x=15
    · simp [P,Q,h]
    · rw [show Q x=ref (actual x) 15 by simp [Q,h],pf,value h]
  have pinj : Injective P := fun {x y} h => (qp x).symm.trans ((congrArg Q h).trans (qp y))
  have qinj : Injective Q := fun {x y} h => (pq x).symm.trans ((congrArg P h).trans (pq y))
  have pfix (x : V) (hx : 6≤x.val) : P x=x := by
    by_cases h : x=15
    · simp [P,h]
    · have eq := rv x h
      have hold := agree (missing x) 15 (by decide) (by simpa [eq] using hx)
      simpa [P,h,eq] using hold.trans eq
  have qfix (x : V) (hx : 6≤x.val) : Q x=x := by simpa [pfix x hx] using qp x
  let g (c : C) (x : V) := Q (f c (P x))
  have gi (c x) : g c (g c x)=x := by simp [g,pq,inv,qp]
  have gn (c x) : g c x≠x := by
    intro h
    exact ne c _ (by simpa [g,pq] using congrArg P h)
  have gp (c d) (cd : c≠d) (x) : g c x≠g d x := fun h => proper c d cd _ (qinj h)
  have gc (x y : V) (xy : x≠y) : ∃ c,g c x=y := by
    obtain ⟨c,h⟩ := cover (P x) (P y) (fun e => xy (pinj e))
    exact ⟨c,by simp [g,h,qp]⟩
  have groot (c) : g c 15=ref c 15 := by simpa [g,P] using qf c
  have held (c x) (h : BoundaryOptions.fixedAt lock c x=true) : g c x=ref c x := by
    by_cases xroot : x=15
    · subst x; exact groot c
    by_cases yroot : ref c x=15
    · have hx : ref c 15=x := by rw [←yroot,ri]
      have eq := groot c
      rw [hx] at eq
      exact ((congrArg (g c) eq.symm).trans (gi c 15)).trans yroot.symm
    · have high : 6≤x.val ∧ 6≤(ref c x).val := by
        have hx : x.val≠15 := fun q => xroot (Fin.ext q)
        have hy : (ref c x).val≠15 := fun q => yroot (Fin.ext q)
        simpa [BoundaryOptions.fixedAt,lock,hx,hy] using h
      simp [g,pfix x high.1,agree c x high.1 high.2,qfix _ high.2]
  have ordinaryP (x : C) : (P (lift x)).val<15 := by
    have h : P (lift x) ≠ 15 := fun eq => by
      have v := pinj (eq.trans (pfix 15 (by decide)).symm)
      have := congrArg (fun a : V => a.val) v
      simp [lift] at this
      omega
    have := (P (lift x)).isLt
    have bad : (P (lift x)).val≠15 := fun q => h (Fin.ext q)
    omega
  let p (x : C) : C := ⟨(P (lift x)).val,ordinaryP x⟩
  have rel (x : C) : P (lift x)=lift (p x) := Fin.ext rfl
  have fixed (x : C) (hx : 6≤x.val) : p x=x := Fin.ext (congrArg (fun a : V => a.val) (pfix (lift x) hx))
  have low (x : C) (hx : x.val<6) : (p x).val<6 := by
    apply Nat.lt_of_not_ge
    intro h
    have unchanged := pfix (P (lift x)) h
    have eq := pinj unchanged
    have val := congrArg (fun a : V => a.val) eq
    change (p x).val=x.val at val
    omega
  have inject : Injective p := by
    intro x y h
    exact Fin.ext (congrArg (fun a : V => a.val) (pinj ((rel x).trans ((congrArg lift h).trans (rel y).symm))))
  have onto (x : C) : ∃ y, p y=x := by
    let v := Q (lift x)
    have h : v≠15 := by
      intro eq
      have both := (pq (lift x)).symm.trans ((congrArg P eq).trans (pfix 15 (by decide)))
      have := congrArg (fun a : V => a.val) both
      change x.val=15 at this
      omega
    have vlt : v.val<15 := by
      have no : v.val≠15 := fun q => h (Fin.ext q)
      have := v.isLt
      omega
    exact ⟨⟨v.val,vlt⟩,Fin.ext (congrArg (fun a : V => a.val) (pq (lift x)))⟩
  exact transport g f P p rel (fun c x => (pq (f c (P x))).symm) fixed low inject onto
    (known g gi gn gp gc held)
/-- The verified Boolean contradiction also covers every assignment of the
six inside missing colors consistent with the nine outside missing colors. -/
def certifyOutside (proof : Array Std.Tactic.BVDecide.LRAT.IntAction) : Option (PLift OutsideFixed) :=
  if ok : Std.Tactic.BVDecide.LRAT.check proof formula then
    some ⟨outside_names (of_certificate proof ok)⟩
  else none
#print axioms outside_names
end InsideNames
