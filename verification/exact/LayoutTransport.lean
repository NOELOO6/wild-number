import LayoutChecks
import Mathlib.GroupTheory.Perm.Sign

namespace WildExact.Seventeen
set_option maxHeartbeats 2500000
set_option maxRecDepth 30000

def layoutSwap (k : Fin 16) : Equiv.Perm Layout :=
  let h (x : Layout) : nextLayout k (nextLayout k x)=x := by
    obtain ⟨b,p⟩ := x
    obtain ⟨one,two,_⟩ := bigFacts k b
    simp [nextLayout,one,two,(smallFacts (branch k b) p).1]
  ⟨nextLayout k,nextLayout k,h,h⟩

def liftOrd (q : Equiv.Perm (Fin 17)) (x : V) : V :=
  Fin.lastCases (Fin.last 17) (fun y => (q y).castSucc) x

private theorem lift_flip (k : Fin 16) (x : V) :
    liftOrd (Equiv.swap k.castSucc k.succ) x=flipV k x := by
  exact (show ∀ (k : Fin 16) (x : V), liftOrd (Equiv.swap k.castSucc k.succ) x=flipV k x from by native_decide) k x

def Realizes (q : Equiv.Perm (Fin 17)) := ∃ e : Equiv.Perm Layout, ∀ l x y,
  sameBlock (e l) (liftOrd q x) (liftOrd q y)=sameBlock l x y

theorem realizes_all (q : Equiv.Perm (Fin 17)) : Realizes q := by
  let S : Submonoid (Equiv.Perm (Fin 17)) := {
    carrier := Realizes
    one_mem' := by
      refine ⟨Equiv.refl _,fun l x y => ?_⟩
      have idv (z : V) : liftOrd 1 z=z := by cases z using Fin.lastCases <;> simp only [liftOrd,Fin.lastCases_last,Fin.lastCases_castSucc,Equiv.Perm.one_apply,Equiv.Perm.mul_apply]
      simp [idv]
    mul_mem' := by
      rintro a b ⟨e,he⟩ ⟨f,hf⟩
      refine ⟨f.trans e,fun l x y => ?_⟩
      have mul (z : V) : liftOrd (a*b) z = liftOrd a (liftOrd b z) := by
        cases z using Fin.lastCases <;> simp only [liftOrd,Fin.lastCases_last,Fin.lastCases_castSucc,Equiv.Perm.one_apply,Equiv.Perm.mul_apply]
      simp [mul,he,hf] }
  have incl : Submonoid.closure (Set.range (fun k : Fin 16 => Equiv.swap k.castSucc k.succ)) ≤ S := by
    apply Submonoid.closure_le.mpr
    rintro _ ⟨k,rfl⟩
    change Realizes _
    refine ⟨layoutSwap k,fun ⟨b,p⟩ x y => ?_⟩
    rw [lift_flip,lift_flip]
    change (tag (smallStep (branch k b) p) (slot (bigStep k b) (flipV k x)) ==
      tag (smallStep (branch k b) p) (slot (bigStep k b) (flipV k y))) = (tag p (slot b x) == tag p (slot b y))
    rw [(bigFacts k b).2.2 x,(bigFacts k b).2.2 y]
    exact (smallFacts (branch k b) p).2 (slot b x) (slot b y)
  rw [Equiv.Perm.mclosure_swap_castSucc_succ] at incl
  exact incl (Submonoid.mem_top q)

/-- Transport all 95,295,200 layout indices under any permutation fixing the extra point. -/
theorem transport (q : Equiv.Perm V) (fixes : q root=root) :
    ∃ e : Equiv.Perm Layout, ∀ l x y, sameBlock (e l) (q x) (q y)=sameBlock l x y := by
  have restrict (p : Equiv.Perm V) (hr : p root=root) (x : Fin 17) : (p x.castSucc).val < 17 := by
    have non : p x.castSucc ≠ Fin.last 17 := fun eq => (Fin.ne_of_lt (Fin.castSucc_lt_last _)) (p.injective (eq.trans hr.symm))
    have := (p x.castSucc).isLt
    have ne : (p x.castSucc).val≠17 := fun eq => non (Fin.ext eq)
    omega
  have inv : q.symm root=root := q.injective (by simp [fixes])
  let trim (p : Equiv.Perm V) (h : p root=root) (x : Fin 17) : Fin 17 := ⟨(p x.castSucc).val,restrict p h x⟩
  have castTrim (p : Equiv.Perm V) (h : p root=root) (x : Fin 17) :
      (trim p h x).castSucc=p x.castSucc := Fin.ext rfl
  let p : Equiv.Perm (Fin 17) := {
    toFun := trim q fixes
    invFun := trim q.symm inv
    left_inv x := Fin.castSucc_injective _ (by rw [castTrim q.symm inv,castTrim q fixes,q.symm_apply_apply])
    right_inv x := Fin.castSucc_injective _ (by rw [castTrim q fixes,castTrim q.symm inv,q.apply_symm_apply]) }
  have same (x : V) : liftOrd p x=q x := by
    cases x using Fin.lastCases with
    | last => simpa only [liftOrd,Fin.lastCases_last] using fixes.symm
    | cast y => simpa only [liftOrd,Fin.lastCases_castSucc] using castTrim q fixes y
  obtain ⟨e,h⟩ := realizes_all p
  exact ⟨e,fun l x y => by simpa only [same] using h l x y⟩

def side (l : Layout) (a b x : V) := sameBlock l x a || sameBlock l x b
def Loss (m : V → V) (l : Layout) := ∃ a b, sameBlock l a b=false ∧ ∀ x, side l a b x=side l a b (m x)

theorem loss_transport (q : Equiv.Perm V) (l s : Layout)
    (shape : ∀ x y, sameBlock s (q x) (q y)=sameBlock l x y) (f g : V → V)
    (maps : ∀ x, q (f x)=g (q x)) : Loss f l ↔ Loss g s := by
  constructor
  · rintro ⟨a,b,ne,h⟩
    refine ⟨q a,q b,(shape a b).trans ne,fun y => ?_⟩
    obtain ⟨x,rfl⟩ := q.surjective y
    simpa only [←maps,side,shape] using h x
  · rintro ⟨a,b,ne,h⟩
    obtain ⟨u,rfl⟩ := q.surjective a
    obtain ⟨v,rfl⟩ := q.surjective b
    refine ⟨u,v,(shape u v).symm.trans ne,fun x => ?_⟩
    simpa only [←maps,side,shape] using h (q x)

#print axioms transport
end WildExact.Seventeen
