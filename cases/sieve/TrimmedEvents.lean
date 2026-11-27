import SizeBounds

namespace WildSieve
open Finset
variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I]

/-- A subdivision retained after all short cuts have been excluded. -/
noncomputable def admissible (J : Finset Nat) (bad : Nat → Finset (Finset V)) (X : Finset V) :
    Finset (Layout X) := by
  classical
  exact univ.filter fun M => ∀ j∈J, ∀ Y∈bad j, ∀ L : Layout Y, ¬ L.val⊆M.val

private theorem inject_short (J : Finset Nat) (bad : Nat → Finset (Finset V)) (X : Finset V)
    (D : Layout (univ : Finset V)) (pass : ∀ j∈J,∀ Y∈bad j,D∉sealEvent Y) (hit : D∈sealEvent X) :
    D∈restrictedSeal (admissible J bad X) := by
  classical
  obtain ⟨M,md⟩ := mem_seal.mp hit
  refine mem_biUnion.mpr ⟨M,mem_filter.mpr ⟨mem_univ _,?_⟩,mem_occurs.mpr md⟩
  exact fun j hj Y hy L sub => pass j hj Y hy (mem_seal.mpr ⟨L,sub.trans md⟩)

/-- The tail budget can count subdivisions of a cut that have survived the
short tests. Its coefficient may depend on the actual set of vertices. -/
theorem trimmed_partition (t : Nat) (total : Fintype.card V=3*t)
    (J K : Finset Nat) (bad : Nat → Finset (Finset V))
    (size : ∀ j∈J∪K,∀ X∈bad j,X.card=3*j) (nonzero : ∀ j∈J,0<j)
    (degree : Nat → Nat → Nat)
    (local_bound : ∀ U z,z∈U → ∀ j∈J,(active (bad j) U z).card≤degree U.card j)
    (h : Nat → ℚ) (positive : ∀ u≤3*t,0<h u)
    (budget : ∀ u,0<u → u≤3*t →
      ∑ j∈J,(degree u j:ℚ)*(sealWeight t j*h (u-3*j)) ≤ h (u-1)-h u)
    (tail : (∑ j∈K, ∑ X∈bad j,((admissible J bad X).card : ℚ) *
      ((ways (t-j):ℚ)/ways t*h (3*t-3*j))) < h (3*t)) :
    ∃ D : Layout (univ : Finset V), ∀ j∈J∪K,∀ X∈bad j,D∉sealEvent X := by
  classical
  letI : Nonempty (Layout (univ : Finset V)) :=
    Fintype.card_pos_iff.mp ((card_layout _ _ (by simpa using total)).symm ▸ ways_pos t)
  let s := @scope V J bad
  let r := @scope V K bad
  let R (i : Events K bad) := admissible J bad (r i)
  let wt (i : Events K bad) : ℚ := ((R i).card:ℚ)*ways (t-i.1.val)/ways t
  have posU (U : Finset V) : 0<h U.card := positive _ (total ▸ U.card_le_univ)
  have sz (j) (hj : j∈J) := size j (mem_union_left K hj)
  have wpos (j) : 0≤sealWeight t j := by exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have shortBound (U : Finset V) (z : V) (hz : z∈U) :
      (∑ i∈through s U z,sealWeight t i.1.val*h (U \ s i).card) ≤ h (U.erase z).card-h U.card := by
    rw [budget_sum J bad sz,card_erase_of_mem hz]
    apply le_trans _ (budget U.card (card_pos.mpr ⟨z,hz⟩) (total ▸ U.card_le_univ))
    apply sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast local_bound U z hz j hj)
      (mul_nonneg (wpos _) (positive _ ((Nat.sub_le _ _).trans (total ▸ U.card_le_univ))).le)
  have endBound : (∑ i:Events K bad,wt i*h (univ \ r i).card) < h (univ : Finset V).card := by
    rw [card_univ,total,Fintype.sum_sigma]
    apply lt_of_le_of_lt _ tail
    rw [← sum_attach K (fun j => ∑ X∈bad j,((admissible J bad X).card:ℚ)*((ways (t-j):ℚ)/ways t*h (3*t-3*j)))]
    apply sum_le_sum
    intro j _
    rw [←sum_attach (bad j.val) (fun X => ((admissible J bad X).card:ℚ)*((ways (t-j.val):ℚ)/ways t*h (3*t-3*j.val)))]
    apply sum_le_sum
    intro X _
    have sx := size j.val (mem_union_right _ j.property) X.val X.property
    change ((admissible J bad X.val).card:ℚ)*ways (t-j.val)/ways t*h (univ \ X.val).card ≤ _
    rw [card_sdiff (subset_univ _),card_univ,total,sx]
    simp only [div_eq_mul_inv,mul_assoc,le_refl]
  obtain ⟨D,pass,rest⟩ := finish s (fun i => sealEvent (s i)) (fun i => sealWeight t i.1.val)
    r (fun i => restrictedSeal (R i)) wt
    (fun i => card_pos.mp (by change 0<i.2.val.card; rw [sz i.1 i.1.property _ i.2.property]; have := nonzero _ i.1.property; omega))
    (fun i => wpos _) (fun i => by exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
    (fun i => seal_lopsided t total s _ _ (sz _ i.1.property _ i.2.property))
    (fun i => restricted_against t total s _ _ (size _ (mem_union_right _ i.1.property) _ i.2.property) _)
    (fun U => h U.card) posU shortBound endBound
  have small (j) (hj : j∈J) (X) (hx : X∈bad j) := pass ⟨⟨j,hj⟩,X,hx⟩
  refine ⟨D,fun j hj X hx => ?_⟩
  rcases mem_union.mp hj with a|b
  · exact small j a X hx
  · exact fun e => rest ⟨⟨j,b⟩,X,hx⟩ (inject_short J bad X D small e)
end WildSieve
