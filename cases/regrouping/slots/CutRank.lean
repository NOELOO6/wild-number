import PaletteBound
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic.Ring

namespace WildSlots
open Finset
variable {I : Type} [Fintype I]
abbrev Perm (I : Type) := Equiv.Perm I

def mark (a b : I → Bool) (p : Perm I) : ℚ := if fits a b p then 1 else 0

/-- A sample detects every weighted sum of cut indicators, including a constant. -/
def Detects (sample : Finset (Perm I)) := ∀ (H : Type) [Fintype H] (a b : H → I → Bool)
  (z : H → ℚ) (s : ℚ), (∀ p∈sample,s + ∑ h,z h * mark (a h) (b h) p=0) →
  ∀ p,s + ∑ h,z h * mark (a h) (b h) p=0

private theorem private_sum {H : Type} [Fintype H] (a b : H → I → Bool) (z : H → ℚ)
    (p : Perm I) (h : H) (unique : ∀ t,fits (a t) (b t) p ↔ t=h) :
    ∑ t,z t * mark (a t) (b t) p=z h := by
  classical
  simp [mark,unique,Finset.sum_ite_eq',Finset.sum_ite_eq]

theorem rank_bound (sample : Finset (Perm I)) (det : Detects sample) (H : Finset (Perm I))
    (a b : ↥H → I → Bool) (priv : ∀ h,∃ p,∀ t,fits (a t) (b t) p ↔ t=h) :
    H.card≤sample.card := by
  classical
  let row (h : ↥H) (p : ↥sample) := mark (a h) (b h) p
  have li : LinearIndependent ℚ row := by
    apply Fintype.linearIndependent_iff.mpr
    intro z hz h
    have values := det (↥H) a b z 0 (fun p hp => by
      simpa [row,Finset.sum_apply] using congrFun hz (⟨p,hp⟩ : ↥sample))
    obtain ⟨p,hp⟩ := priv h
    simpa only [zero_add,private_sum a b z p h hp] using values p
  simpa only [Module.finrank_pi,Fintype.card_coe] using li.fintype_card_le_finrank

/-- An overlap allows the constant function to be counted as one additional
independent row. The cover is otherwise a disjoint family of sets. -/
theorem rank_bound_overlap (sample : Finset (Perm I)) (det : Detects sample) (H : Finset (Perm I))
    (a b : ↥H → I → Bool) (priv : ∀ h,∃ p,∀ t,fits (a t) (b t) p ↔ t=h)
    (p : Perm I) (overlap : 2≤(univ.filter (fun h => fits (a h) (b h) p)).card) :
    H.card+1≤sample.card := by
  classical
  let row : Option (↥H) → ↥sample → ℚ
    | none,_ => 1
    | some h,q => mark (a h) (b h) q
  have li : LinearIndependent ℚ row := by
    apply Fintype.linearIndependent_iff.mpr
    intro z hz
    have values := det (↥H) a b (fun h => z (some h)) (z none) (fun q hq => by
      simpa [row,Finset.sum_apply,Fintype.sum_option] using congrFun hz (⟨q,hq⟩ : ↥sample))
    have equal (h : ↥H) : z (some h)= -z none := by
      obtain ⟨w,hw⟩ := priv h
      have eq := values w
      rw [private_sum a b _ w h hw] at eq
      exact eq_neg_of_add_eq_zero_left (by rwa [add_comm])
    let count := (univ.filter (fun h => fits (a h) (b h) p)).card
    have ones : ∑ h,mark (a h) (b h) p=(count : ℚ) := by
      simp [mark,count,Finset.sum_boole]
    have eq := values p
    simp_rw [equal] at eq
    rw [←Finset.mul_sum,ones] at eq
    have product : z none * (1-(count : ℚ))=0 := by
      rw [←eq]
      ring
    have nonzero : (1:ℚ)-(count:ℚ)≠0 := sub_ne_zero.mpr (by exact_mod_cast (show 1≠count by omega))
    have base : z none=0 := (mul_eq_zero.mp product).resolve_right nonzero
    intro i
    cases i with
    | none => exact base
    | some h => simp [equal,base]
  simpa only [Module.finrank_pi,Fintype.card_option,Fintype.card_coe] using li.fintype_card_le_finrank

/-- A small detecting sample gives a local-to-global test for any number of slots. -/
theorem palette_from_sample {V C : Type} (sample : Finset (Perm I)) (det : Detects sample)
    (E : C → V → V → Prop) (sym : ∀ c {x y},E c x y → E c y x) (u v : I → V) :
    (∃ p : Perm I,passes E u v (assign p)) ↔
      ∀ S : Finset C,S.card≤sample.card → ∃ p : Perm I,∀ c∈S,WildDeletion.Connected (extend (E c) u v (assign p)) :=
  palette_from_covers sample.card (fun H a b _ priv => rank_bound sample det H a b priv) E sym u v

end WildSlots
