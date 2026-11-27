import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

namespace WildSieve
open Finset
variable {V I : Type} [DecidableEq V] [Fintype I]

def through (support : I → Finset V) (U : Finset V) (z : V) : Finset I := by
  classical
  exact univ.filter fun i => support i ⊆ U ∧ z ∈ support i

private theorem in_through {support : I → Finset V} {U : Finset V} {z : V} {i : I} :
    i ∈ through support U z ↔ support i ⊆ U ∧ z ∈ support i := by
  classical
  simp [through]

/-- A finite avoidance sieve. Z(U) is the mass avoiding every short event
supported in U. The first inequality charges a loss at z to its possible
events. H is any positive comparison function satisfying the second inequality.
No infinite-volume or uniform branching assumption is used. -/
theorem ratios (support : I → Finset V) (weight : I → ℚ)
    (Z H : Finset V → ℚ) (hZ : ∀ U, 0 ≤ Z U) (hH : ∀ U, 0 < H U)
    (hw : ∀ i, 0 ≤ weight i)
    (loss : ∀ U z, z ∈ U → Z (U.erase z) - Z U ≤
      ∑ i ∈ through support U z, weight i * Z (U \ support i))
    (budget : ∀ U z, z ∈ U →
      ∑ i ∈ through support U z, weight i * H (U \ support i) ≤ H (U.erase z) - H U)
    (U T : Finset V) (sub : T ⊆ U) : H U * Z T ≤ H T * Z U := by
  classical
  induction U using Finset.strongInductionOn generalizing T with
  | _ U ih =>
    by_cases eq : T=U
    · simp [eq]
    obtain ⟨z,hz,notT⟩ : ∃ z ∈ U, z ∉ T := by
      by_contra! h
      exact eq (Subset.antisymm sub h)
    let A := U.erase z
    have lt : A ⊂ U := erase_ssubset hz
    have inner (i : I) (hi : i ∈ through support U z) : U \ support i ⊆ A := by
      have ins := in_through.mp hi
      intro v hv
      obtain ⟨inU,out⟩ := mem_sdiff.mp hv
      exact mem_erase.mpr ⟨fun vz => out (vz ▸ ins.2),inU⟩
    have part (i : I) (hi : i ∈ through support U z) :
        H A * (weight i * Z (U \ support i)) ≤ (weight i * H (U \ support i)) * Z A := by
      have p := mul_le_mul_of_nonneg_left (ih A lt _ (inner i hi)) (hw i)
      simpa only [mul_left_comm,mul_assoc,mul_comm] using p
    have parts := Finset.sum_le_sum part
    rw [← Finset.mul_sum,← Finset.sum_mul] at parts
    have l := mul_le_mul_of_nonneg_left (loss U z hz) (hH A).le
    have b := mul_le_mul_of_nonneg_right (budget U z hz) (hZ A)
    change H A * (Z A - Z U) ≤ _ at l
    change _ ≤ (H A - H U) * Z A at b
    have step : H U * Z A ≤ H A * Z U := by linarith only [l.trans (parts.trans b)]
    have prior := ih A lt T (fun v hv => mem_erase.mpr ⟨fun eq => notT (eq ▸ hv),sub hv⟩)
    have h1 := mul_le_mul_of_nonneg_left prior (hH U).le
    have h2 := mul_le_mul_of_nonneg_left step (hH T).le
    apply le_of_mul_le_mul_left (a := H A) _ (hH A)
    calc
      H A * (H U * Z T) = H U * (H A * Z T) := by ac_rfl
      _ ≤ H U * (H T * Z A) := h1
      _ = H T * (H U * Z A) := by ac_rfl
      _ ≤ H T * (H A * Z U) := h2
      _ = H A * (H T * Z U) := by ac_rfl
end WildSieve
