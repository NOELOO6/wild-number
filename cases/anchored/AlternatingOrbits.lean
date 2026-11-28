import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Prod

namespace WildAnchor.Alternating
open Function Finset

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Two fixed-point-free involutions, with their alternating two-step walk. -/
structure Pairing (V : Type) where
  first : V → V
  second : V → V
  first_inv : Involutive first
  second_inv : Involutive second
  first_moves : ∀ x,first x≠x
  second_moves : ∀ x,second x≠x

namespace Pairing
variable (P : Pairing V)

def step (x : V) := P.first (P.second x)
def point (x : V) (i : Nat) := P.step^[i] x
noncomputable def period (x : V) := minimalPeriod P.step x

omit [Fintype V] [DecidableEq V] in
theorem point_succ (x : V) (i : Nat) : P.point x (i+1)=P.first (P.second (P.point x i)) :=
  Function.iterate_succ_apply' _ _ _

omit [Fintype V] [DecidableEq V] in
private theorem reflect_step (x : V) (i : Nat) :
    P.first (P.point x (i+1))=P.second (P.point x i) := by rw [point_succ,P.first_inv]

omit [Fintype V] [DecidableEq V] in
private theorem disjoint_forward (x : V) (d i : Nat) :
    P.first (P.point x i)≠P.point x (i+d) := by
  induction d using Nat.strong_induction_on generalizing i with
  | h d ih =>
    intro eq
    match d with
    | 0 => exact P.first_moves _ eq
    | 1 =>
      have e := congrArg P.first eq
      rw [P.first_inv,reflect_step] at e
      exact P.second_moves _ e.symm
    | d+2 =>
      apply ih d (by omega) (i+1)
      have e := congrArg P.first eq
      rw [P.first_inv,show i+(d+2)=(i+d+1)+1 by omega,reflect_step] at e
      rw [reflect_step,e,P.second_inv,show i+1+d=i+d+1 by omega]

omit [Fintype V] [DecidableEq V] in
theorem opposite_disjoint (x : V) (i j : Nat) : P.first (P.point x i)≠P.point x j := by
  rcases le_total i j with h|h
  · simpa only [Nat.add_sub_of_le h] using P.disjoint_forward x (j-i) i
  · intro eq
    have no := P.disjoint_forward x (i-j) j
    rw [Nat.add_sub_of_le h] at no
    exact no ((congrArg P.first eq).symm.trans (P.first_inv _))

omit [DecidableEq V] in
theorem period_pos (x : V) : 0<P.period x :=
  minimalPeriod_pos_of_mem_periodicPts ((P.first_inv.injective.comp P.second_inv.injective).mem_periodicPts x)

omit [Fintype V] [DecidableEq V] in
theorem point_mod (x : V) (j : Nat) : P.point x (j%P.period x)=P.point x j :=
  iterate_mod_minimalPeriod_eq

def endpoint (x : V) (z : Fin (P.period x) × Bool) :=
  if z.2 then P.first (P.point x z.1.val) else P.point x z.1.val

omit [Fintype V] [DecidableEq V] in
theorem endpoint_inj (x : V) : Injective (P.endpoint x) := by
  rintro ⟨i,b⟩ ⟨j,c⟩ eq
  have same {l k : Fin (P.period x)} (h : P.point x l.val=P.point x k.val) : l=k :=
    Fin.ext ((iterate_eq_iterate_iff_of_lt_minimalPeriod l.isLt k.isLt).mp h)
  cases b <;> cases c <;> simp only [endpoint,Bool.false_eq_true,if_false,if_true,Prod.mk.injEq,
    true_and,and_true] at eq ⊢
  · exact same eq
  · exact False.elim (P.opposite_disjoint x _ _ eq.symm)
  · exact False.elim (P.opposite_disjoint x _ _ eq)
  · exact same (P.first_inv.injective eq)

noncomputable def component (x : V) := univ.image (P.endpoint x)

omit [Fintype V] in
theorem mem_component (x v : V) : v∈P.component x ↔
    ∃ i<P.period x,v=P.point x i ∨ v=P.first (P.point x i) := by
  constructor
  · rintro hv
    obtain ⟨⟨i,b⟩,_,rfl⟩ := mem_image.mp hv
    exact ⟨i,i.isLt,by cases b <;> simp [endpoint]⟩
  · rintro ⟨i,hi,e|e⟩
    · exact mem_image.mpr ⟨(⟨i,hi⟩,false),mem_univ _,e.symm⟩
    · exact mem_image.mpr ⟨(⟨i,hi⟩,true),mem_univ _,e.symm⟩

omit [Fintype V] in
theorem component_card (x : V) : (P.component x).card=2*P.period x := by
  rw [component,card_image_of_injective _ (P.endpoint_inj x)]
  simp [Fintype.card_prod,Nat.mul_comm]

omit [Fintype V] [DecidableEq V] in
theorem advance (x : V) (i : Nat) :
    P.second (P.point x i)=P.first (P.point x ((i+1)%P.period x)) := by
  rw [point_mod,reflect_step]

theorem component_closed (x : V) :
    (∀ v∈P.component x,P.first v∈P.component x) ∧ (∀ v∈P.component x,P.second v∈P.component x) := by
  have pos := P.period_pos x
  constructor <;> intro v hv <;> obtain ⟨i,hi,rfl|rfl⟩ := (P.mem_component ..).mp hv
  · exact (P.mem_component ..).mpr ⟨i,hi,Or.inr rfl⟩
  · exact (P.mem_component ..).mpr ⟨i,hi,Or.inl (P.first_inv _)⟩
  · exact (P.mem_component ..).mpr ⟨_,Nat.mod_lt _ pos,Or.inr (P.advance x i)⟩
  · let j := if i=0 then P.period x-1 else i-1
    have hl : j<P.period x := by dsimp [j]; split <;> omega
    have back : (j+1)%P.period x=i := by
      dsimp [j]; split
      · rename_i h; rw [h,show P.period x-1+1=P.period x by omega,Nat.mod_self]
      · rw [show i-1+1=i by omega,Nat.mod_eq_of_lt hi]
    have e := P.advance x j
    rw [back] at e
    exact (P.mem_component ..).mpr ⟨j,hl,Or.inl (e ▸ P.second_inv _)⟩

omit [Fintype V] in
theorem component_subset (U : Finset V) (x : V) (hx : x∈U)
    (ha : ∀ v∈U,P.first v∈U) (hb : ∀ v∈U,P.second v∈U) : P.component x⊆U := by
  have inside (i : Nat) : P.point x i∈U := by
    induction i with
    | zero => exact hx
    | succ i ih => rw [point_succ];exact ha _ (hb _ ih)
  intro v hv
  obtain ⟨i,_,rfl|rfl⟩ := (P.mem_component ..).mp hv
  · exact inside i
  · exact ha _ (inside i)

end Pairing
end WildAnchor.Alternating
