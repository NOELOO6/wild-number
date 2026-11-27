import FiniteSieve

namespace WildSieve
open Finset
variable {V I J Ω : Type} [DecidableEq V] [Fintype I] [Fintype J] [Fintype Ω] [DecidableEq Ω]

noncomputable def avoid (s : I → Finset V) (E : I → Finset Ω) (U : Finset V) : Finset Ω := by
  classical
  exact univ.filter fun x => ∀ i, s i ⊆ U → x ∉ E i

theorem mem_avoid {s : I → Finset V} {E : I → Finset Ω} {U : Finset V} {x : Ω} :
    x ∈ avoid s E U ↔ ∀ i, s i ⊆ U → x ∉ E i := by
  classical
  simp [avoid]

private theorem avoid_anti (s : I → Finset V) (E : I → Finset Ω) {A B : Finset V}
    (sub : A ⊆ B) : avoid s E B ⊆ avoid s E A :=
  fun _ h => mem_avoid.mpr (fun i hi => mem_avoid.mp h i (hi.trans sub))

omit [Fintype Ω] in
private theorem card_cover {K : Type} {t : Finset K} {A : Finset Ω} (f : K → Finset Ω)
    (h : ∀ x ∈ A, ∃ i ∈ t, x ∈ f i) : (A.card : ℚ) ≤ ∑ i ∈ t, ((f i).card : ℚ) := by
  have sub : A ⊆ t.biUnion f := fun x hx => mem_biUnion.mpr (h x hx)
  exact_mod_cast (Finset.card_le_card sub).trans (Finset.card_biUnion_le)

/-- A lopsided bound for a specified event against all short events whose
supports are contained in a disjoint set. Cardinalities are unnormalized. -/
def Against (s : I → Finset V) (E : I → Finset Ω) (t : Finset V) (F : Finset Ω) (p : ℚ) :=
  ∀ U, Disjoint t U → ((F ∩ avoid s E U).card : ℚ) ≤ p * (avoid s E U).card

theorem loss_from_events (s : I → Finset V) (E : I → Finset Ω) (p : I → ℚ)
    (lop : ∀ i, Against s E (s i) (E i) (p i)) (U : Finset V) (z : V) (_hz : z ∈ U) :
    ((avoid s E (U.erase z)).card : ℚ) - (avoid s E U).card ≤
      ∑ i ∈ through s U z, p i * (avoid s E (U \ s i)).card := by
  classical
  let A := avoid s E (U.erase z)
  let B := avoid s E U
  have sub : B ⊆ A := avoid_anti s E (erase_subset z U)
  have hit (x) (hx : x ∈ A \ B) : ∃ i ∈ through s U z, x ∈ E i ∩ avoid s E (U \ s i) := by
    obtain ⟨ha,hb⟩ := mem_sdiff.mp hx
    change x ∉ avoid s E U at hb
    rw [mem_avoid] at hb
    push_neg at hb
    obtain ⟨i,hi,ei⟩ := hb
    have zi : z ∈ s i := by
      by_contra nz
      apply mem_avoid.mp ha i _ ei
      intro v hv
      exact mem_erase.mpr ⟨fun eq => nz (eq ▸ hv),hi hv⟩
    refine ⟨i,by simp [through,hi,zi],mem_inter.mpr ⟨ei,?_⟩⟩
    apply avoid_anti s E _ ha
    intro v hv
    obtain ⟨inU,out⟩ := mem_sdiff.mp hv
    exact mem_erase.mpr ⟨fun eq => out (eq ▸ zi),inU⟩
  have counted := card_cover (fun i => E i ∩ avoid s E (U \ s i)) hit
  have bound := Finset.sum_le_sum (s := through s U z) (fun i _ =>
    lop i (U \ s i) Finset.disjoint_sdiff)
  have dif := Finset.card_sdiff sub
  have le := Finset.card_le_card sub
  have rat : ((A \ B).card : ℚ) = A.card - B.card := by
    rw [dif,Nat.cast_sub le]
  rw [← rat]
  exact counted.trans bound

/-- Avoid a second family once every short-event ratio is controlled.
Every hypothesis is stated for finite sets of outcomes and rational weights. -/
theorem finish [Fintype V] [Nonempty Ω] (s : I → Finset V) (E : I → Finset Ω)
    (p : I → ℚ) (t : J → Finset V) (F : J → Finset Ω) (q : J → ℚ)
    (ne : ∀ i, (s i).Nonempty) (hp : ∀ i, 0 ≤ p i) (hq : ∀ j, 0 ≤ q j)
    (short : ∀ i, Against s E (s i) (E i) (p i))
    (long : ∀ j, Against s E (t j) (F j) (q j))
    (H : Finset V → ℚ) (pos : ∀ U, 0 < H U)
    (budget : ∀ U z, z ∈ U →
      ∑ i ∈ through s U z, p i * H (U \ s i) ≤ H (U.erase z) - H U)
    (tail : ∑ j, q j * H (univ \ t j) < H univ) :
    ∃ x, (∀ i, x ∉ E i) ∧ ∀ j, x ∉ F j := by
  classical
  let Z (U : Finset V) : ℚ := (avoid s E U).card
  have nonneg (U) : 0 ≤ Z U := Nat.cast_nonneg _
  have control := ratios s p Z H nonneg pos hp (loss_from_events s E p short) budget
  have empty : avoid s E ∅ = univ := by
    apply eq_univ_of_forall
    intro x
    exact mem_avoid.mpr (fun i hi => False.elim ((ne i).ne_empty (subset_empty.mp hi)))
  have positive : 0 < Z univ := by
    have start := control univ ∅ (empty_subset _)
    have z0 : 0 < Z ∅ := by simp [Z,empty,Fintype.card_pos]
    exact pos_of_mul_pos_right ((mul_pos (pos univ) z0).trans_le start) (pos ∅).le
  by_contra! failed
  have cover (x) (hx : x ∈ avoid s E univ) : ∃ j ∈ (univ : Finset J), x ∈ F j ∩ avoid s E (univ \ t j) := by
    obtain ⟨j,hj⟩ := failed x (fun i => mem_avoid.mp hx i (subset_univ _))
    exact ⟨j,mem_univ _,mem_inter.mpr ⟨hj,avoid_anti s E (subset_univ _) hx⟩⟩
  have c := card_cover (fun j => F j ∩ avoid s E (univ \ t j)) cover
  have w := Finset.sum_le_sum (s := (univ : Finset J)) (fun j _ => long j (univ \ t j) Finset.disjoint_sdiff)
  have mass : Z univ ≤ ∑ j, q j * Z (univ \ t j) := c.trans w
  have ratiosum := Finset.sum_le_sum (s := (univ : Finset J)) (fun j _ =>
    mul_le_mul_of_nonneg_left (control univ (univ \ t j) (subset_univ _)) (hq j))
  have rhs : H univ * (∑ j, q j * Z (univ \ t j)) ≤ (∑ j, q j * H (univ \ t j)) * Z univ := by
    rw [Finset.mul_sum,Finset.sum_mul]
    simpa only [mul_comm,mul_left_comm,mul_assoc] using ratiosum
  exact (not_lt_of_ge ((mul_le_mul_of_nonneg_left mass (pos univ).le).trans rhs))
    (mul_lt_mul_of_pos_right tail positive)
end WildSieve
