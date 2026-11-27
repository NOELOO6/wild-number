import PairFibers
import Mathlib.Data.Fintype.Prod

namespace WildAnchor
open Finset
variable {I J : Type} [Fintype I] [DecidableEq I]
abbrev Pts (I : Type) := I × Bool

def flag (s : State I) (x : Pts I) := if x.2 then (s x.1).2 else (s x.1).1
def state (f : Pts I → Bool) : State I := fun i => (f (i,false),f (i,true))
omit [Fintype I] [DecidableEq I] in
@[simp] theorem flag_state (f : Pts I → Bool) (x : Pts I) : flag (state f) x=f x := by
  rcases x with ⟨i,b⟩; cases b <;> rfl

def perm (q : Shuffle I) : Pts I ≃ Pts I where
  toFun x := (q.1 x.1,xor x.2 (q.2 x.1))
  invFun y := (q.1.symm y.1,xor y.2 (q.2 (q.1.symm y.1)))
  left_inv x := by rcases x with ⟨i,b⟩; simp
  right_inv y := by rcases y with ⟨i,b⟩; simp

omit [Fintype I] [DecidableEq I] in
theorem fits_iff (q : Shuffle I) (s t : State I) :
    Fits q s t ↔ ∀ x,flag s x=flag t (perm q x) := by
  constructor
  · intro h x
    rcases x with ⟨i,b⟩
    have eq := h i
    change (if b then (s i).2 else (s i).1)=(if xor b (q.2 i) then (t (q.1 i)).2 else (t (q.1 i)).1)
    rw [←eq]
    cases b <;> cases hbit : q.2 i <;> simp [flip,hbit]
  · intro h i
    have a := h (i,false)
    have b := h (i,true)
    cases hbit : q.2 i <;> apply Prod.ext <;> simp_all [flag,perm,flip]

def transport (q : Shuffle I) (s : State I) := state fun x => flag s ((perm q).symm x)

omit [DecidableEq I] in
theorem width_transport (q : Shuffle I) (s : State I) (j : Fin 3) :
    width (transport q s) j=width s j := by
  classical
  have fit : Fits q s (transport q s) := (fits_iff ..).mpr (fun x => by simp [transport])
  have eq (i) : kind ((transport q s) (q.1 i))=kind (s i) := by
    rw [←fit i]
    rcases s i with ⟨a,b⟩
    cases a <;> cases b <;> cases q.2 i <;> decide
  unfold width
  apply card_bij (fun i _ => q.1.symm i)
  · intro i hi
    exact mem_filter.mpr ⟨mem_univ _,(eq _).symm.trans (by simpa using (mem_filter.mp hi).2)⟩
  · intro _ _ _ _ h
    exact q.1.symm.injective h
  · intro i hi
    exact ⟨q.1 i,mem_filter.mpr ⟨mem_univ _,(eq i).trans (mem_filter.mp hi).2⟩,q.1.symm_apply_apply _⟩

/-- First-moment certificate under permutations of the anchor pairs. Each
color may use a different coordinate system and a different list of cuts. -/
theorem choose_shuffle {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (s : A → State I) (t : C → B → State I) (coords : C → Shuffle I)
    (budget : (∑ c,∑ a,∑ b,price (s a) (t c b)) < (Fintype.card I).factorial * 2^Fintype.card I) :
    ∃ p : Shuffle I,∀ c a b,¬Fits p (s a) (transport (coords c) (t c b)) := by
  classical
  let bad (c : C) (a : A) (b : B) := univ.filter (fun p : Shuffle I => Fits p (s a) (transport (coords c) (t c b)))
  let cover := univ.biUnion fun c : C => univ.biUnion fun a : A => univ.biUnion fun b : B => bad c a b
  have bound : cover.card≤∑ c,∑ a,∑ b,price (s a) (t c b) := by
    apply card_biUnion_le.trans
    apply sum_le_sum; intro c _
    apply card_biUnion_le.trans
    apply sum_le_sum; intro a _
    apply card_biUnion_le.trans
    apply sum_le_sum; intro b _
    simpa only [price,width_transport] using fiber_price (s a) (transport (coords c) (t c b))
  have full : (univ : Finset (Shuffle I)).card=(Fintype.card I).factorial*2^Fintype.card I := by
    simp [Shuffle,Fintype.card_prod,Fintype.card_perm]
  obtain ⟨p,_,hp⟩ := exists_mem_not_mem_of_card_lt_card (s:=cover) (t:=univ)
    (show cover.card<(univ : Finset (Shuffle I)).card by rw [full];exact bound.trans_lt budget)
  exact ⟨p,fun c a b fits => hp (mem_biUnion.mpr ⟨c,mem_univ _,mem_biUnion.mpr ⟨a,mem_univ _,
    mem_biUnion.mpr ⟨b,mem_univ _,mem_filter.mpr ⟨mem_univ _,fits⟩⟩⟩⟩)⟩

end WildAnchor
