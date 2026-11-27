import ClosedEvents

namespace WildSieve
open Finset
variable {V : Type} [Fintype V] [DecidableEq V]

abbrev Events (J : Finset Nat) (bad : Nat → Finset (Finset V)) :=
  (j : ↥J) × ↥(bad j.val)

def scope {J : Finset Nat} {bad : Nat → Finset (Finset V)} (e : Events J bad) := e.2.val

def active (B : Finset (Finset V)) (U : Finset V) (z : V) := B.filter (fun X => X ⊆ U ∧ z ∈ X)

omit [Fintype V] in
theorem budget_sum (J : Finset Nat) (bad : Nat → Finset (Finset V))
    (size : ∀ j ∈ J, ∀ X ∈ bad j, X.card=3*j) (w h : Nat → ℚ) (U : Finset V) (z : V) :
    (∑ i ∈ through (@scope V J bad) U z, w i.1.val * h (U \ scope i).card) =
      ∑ j ∈ J, ((active (bad j) U z).card : ℚ) * (w j * h (U.card-3*j)) := by
  classical
  have each (j : ↥J) :
      ∑ i : ↥(bad j.val), (if i.val ⊆ U ∧ z ∈ i.val then w j * h (U \ i.val).card else 0) =
        ((active (bad j) U z).card : ℚ) * (w j * h (U.card-3*j)) := by
    rw [Finset.univ_eq_attach,Finset.sum_attach (bad j) (fun X => if X ⊆ U ∧ z ∈ X then w j * h (U \ X).card else 0)]
    rw [← Finset.sum_filter]
    calc
      _ = ∑ _ ∈ active (bad j) U z,w j * h (U.card-3*j) := by
        apply sum_congr rfl
        intro X hx
        rw [card_sdiff (mem_filter.mp hx).2.1,size j j.property X (mem_filter.mp hx).1]
      _ = _ := by simp [nsmul_eq_mul]
  rw [through,Finset.sum_filter,Fintype.sum_sigma]
  simp only [scope] at *
  exact (sum_congr rfl (fun j _ => each j)).trans (by rw [Finset.univ_eq_attach]; exact Finset.sum_attach J (fun j => ((active (bad j) U z).card : ℚ) * (w j * h (U.card-3*j))))

theorem partition_split (t : Nat) (total : Fintype.card V=3*t)
    (J K : Finset Nat) (bad rest : Nat → Finset (Finset V))
    (shortSize : ∀ j∈J,∀ X∈bad j,X.card=3*j)
    (longSize : ∀ j∈K,∀ X∈rest j,X.card=3*j) (nonzero : ∀ j ∈ J, 0 < j)
    (degree : Nat → Nat → Nat) (count : Nat → Nat)
    (local_bound : ∀ U z, z ∈ U → ∀ j ∈ J, (active (bad j) U z).card ≤ degree U.card j)
    (global_bound : ∀ j ∈ K,(rest j).card ≤ count j)
    (h : Nat → ℚ) (positive : ∀ u ≤ 3*t,0 < h u)
    (budget : ∀ u, 0 < u → u ≤ 3*t →
      ∑ j ∈ J,(degree u j : ℚ) * (sealWeight t j * h (u-3*j)) ≤ h (u-1) - h u)
    (tail : (∑ j ∈ K,(count j : ℚ) * (sealWeight t j * h (3*t-3*j))) < h (3*t)) :
    ∃ D : Layout (univ : Finset V), (∀ j∈J,∀ X∈bad j,D∉sealEvent X) ∧ ∀ j∈K,∀ X∈rest j,D∉sealEvent X := by
  classical
  letI : Nonempty (Layout (univ : Finset V)) :=
    Fintype.card_pos_iff.mp ((card_layout _ _ (by simpa using total)).symm ▸ ways_pos t)
  let s := @scope V J bad
  let r := @scope V K rest
  have posU (U : Finset V) : 0 < h U.card :=
    positive _ (total ▸ Finset.card_le_univ U)
  have wpos (j) : 0 ≤ sealWeight t j := by exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have shortBound (U : Finset V) (z : V) (hz : z∈U) :
      (∑ i ∈ through s U z,sealWeight t i.1.val * h (U \ s i).card) ≤ h (U.erase z).card-h U.card := by
    rw [budget_sum J bad shortSize,card_erase_of_mem hz]
    apply le_trans _ (budget U.card (card_pos.mpr ⟨z,hz⟩) (total ▸ U.card_le_univ))
    apply sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast local_bound U z hz j hj)
      (mul_nonneg (wpos _) (positive _ ((Nat.sub_le _ _).trans (total ▸ U.card_le_univ))).le)
  have longBound : (∑ i : Events K rest,sealWeight t i.1.val * h (univ \ r i).card) < h (univ : Finset V).card := by
    rw [card_univ,total,Fintype.sum_sigma]
    apply lt_of_le_of_lt _ tail
    rw [← Finset.sum_attach K (fun j => (count j : ℚ) * (sealWeight t j * h (3*t-3*j)))]
    apply sum_le_sum
    intro j _
    have eq : ∀ i : ↥(rest j.val), (univ \ i.val).card=3*t-3*j.val := by
      intro i
      rw [card_sdiff (subset_univ _),card_univ,total,longSize j j.property i.val i.property]
    simp only [r,scope,eq,Finset.sum_const,card_univ,Fintype.card_coe,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast global_bound j j.property)
      (mul_nonneg (wpos _) (positive _ (Nat.sub_le _ _)).le)
  obtain ⟨D,pass,others⟩ := finish s (fun i => sealEvent (s i)) (fun i => sealWeight t i.1.val)
    r (fun i => sealEvent (r i)) (fun i => sealWeight t i.1.val)
    (fun i => card_pos.mp (by change 0 < i.2.val.card; rw [shortSize i.1 i.1.property _ i.2.property]; have := nonzero _ i.1.property; omega))
    (fun i => wpos _) (fun i => wpos _)
    (fun i => seal_lopsided t total s _ _ (shortSize _ i.1.property _ i.2.property))
    (fun i => seal_lopsided t total s _ _ (longSize _ i.1.property _ i.2.property))
    (fun U => h U.card) posU shortBound longBound
  exact ⟨D,fun j hj X hx => pass ⟨⟨j,hj⟩,X,hx⟩,fun j hj X hx => others ⟨⟨j,hj⟩,X,hx⟩⟩

theorem partition_from_counts (t : Nat) (total : Fintype.card V=3*t)
    (J K : Finset Nat) (bad : Nat → Finset (Finset V))
    (size : ∀ j ∈ J ∪ K, ∀ X ∈ bad j, X.card=3*j) (nonzero : ∀ j ∈ J, 0 < j)
    (degree : Nat → Nat → Nat) (count : Nat → Nat)
    (local_bound : ∀ U z, z ∈ U → ∀ j ∈ J, (active (bad j) U z).card ≤ degree U.card j)
    (global_bound : ∀ j ∈ K,(bad j).card ≤ count j)
    (h : Nat → ℚ) (positive : ∀ u ≤ 3*t,0 < h u)
    (budget : ∀ u, 0 < u → u ≤ 3*t →
      ∑ j ∈ J,(degree u j : ℚ) * (sealWeight t j * h (u-3*j)) ≤ h (u-1) - h u)
    (tail : (∑ j ∈ K,(count j : ℚ) * (sealWeight t j * h (3*t-3*j))) < h (3*t)) :
    ∃ D : Layout (univ : Finset V), ∀ j ∈ J ∪ K, ∀ X ∈ bad j, D ∉ sealEvent X := by
  obtain ⟨D,first,last⟩ := partition_split t total J K bad bad (fun j hj => size j (mem_union_left K hj))
    (fun j hj => size j (mem_union_right J hj)) nonzero degree count local_bound global_bound h positive budget tail
  exact ⟨D,fun j hj => (mem_union.mp hj).elim (first j) (last j)⟩
end WildSieve
