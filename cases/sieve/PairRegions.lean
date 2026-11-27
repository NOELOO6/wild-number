import LocalSeals
namespace WildSieve
open Finset
variable {I V : Type} [DecidableEq I] [DecidableEq V]

def points (edge : I → Finset V) (S : Finset I) := S.biUnion edge

omit [DecidableEq I] in
theorem points_mono (edge : I → Finset V) {S T : Finset I} (sub : S⊆T) : points edge S⊆points edge T := by
  intro x hx
  obtain ⟨i,hi,xi⟩ := mem_biUnion.mp hx
  exact mem_biUnion.mpr ⟨i,sub hi,xi⟩

omit [DecidableEq I] in
theorem points_size (P : Finset I) (edge : I → Finset V) (sz : ∀ i∈P,(edge i).card=2)
    (apart : (P : Set I).PairwiseDisjoint edge) {S : Finset I} (sp : S⊆P) :
    (points edge S).card=2*S.card := by
  rw [points,card_biUnion (fun _ h _ k ne => apart (sp h) (sp k) ne),sum_congr rfl (fun i hi => sz i (sp hi))]
  simp [Nat.mul_comm]

theorem points_common (P : Finset I) (edge : I → Finset V) (apart : (P : Set I).PairwiseDisjoint edge)
    {S T : Finset I} (sp : S⊆P) (tp : T⊆P) : points edge S ∩ points edge T=points edge (S∩T) := by
  ext v
  constructor
  · intro e
    obtain ⟨i,hi,vi⟩ := mem_biUnion.mp (mem_inter.mp e).1
    obtain ⟨j,hj,vj⟩ := mem_biUnion.mp (mem_inter.mp e).2
    have ij : i=j := by
      by_contra ne
      exact disjoint_left.mp (apart (sp hi) (tp hj) ne) vi vj
    exact mem_biUnion.mpr ⟨j,mem_inter.mpr ⟨ij ▸ hi,hj⟩,vj⟩
  · intro e
    exact mem_inter.mpr ⟨points_mono edge inter_subset_left e,points_mono edge inter_subset_right e⟩

variable [Fintype V]

noncomputable def sixHits (X : Finset V) (P : Finset I) (edge : I → Finset V) :=
  (P.powersetCard 3).biUnion (fun S => localSeal X (points edge S))

/-- Count all six-point cuts formed by three matching edges. Distinct such
cuts can occur together only when the index triples are disjoint. -/
theorem six_coverage (X : Finset V) (P : Finset I) (edge : I → Finset V)
    (sz : ∀ i∈P,(edge i).card=2) (apart : (P : Set I).PairwiseDisjoint edge)
    (inside : points edge P⊆X) (j : Nat) (len : X.card=3*j) (lo : 4≤j) :
    2*(P.card.choose 3*(10*ways (j-2))) ≤ 2*(sixHits X P edge).card+
      P.card.choose 3 * (P.card-3).choose 3 * (100*ways (j-4)) := by
  classical
  let S := P.powersetCard 3
  let E (s : Finset I) := localSeal X (points edge s)
  have each (s) (hs : s∈S) : (E s).card=10*ways (j-2) := by
    obtain ⟨sub,three⟩ := mem_powersetCard.mp hs
    have os := points_size P edge sz apart sub
    rw [three] at os
    exact local_seal_card X _ 2 (j-2) ((points_mono edge sub).trans inside) (by omega) (by omega)
  have pair (s) (hs : s∈S) (t) (ht : t∈S) : (if s=t then 0 else (E s∩E t).card) ≤
      if Disjoint s t then 100*ways (j-4) else 0 := by
    obtain ⟨sp,sc⟩ := mem_powersetCard.mp hs
    obtain ⟨tp,tc⟩ := mem_powersetCard.mp ht
    have ssz := points_size P edge sz apart sp
    have tsz := points_size P edge sz apart tp
    rw [sc] at ssz
    rw [tc] at tsz
    by_cases same : s=t
    · simp [same]
    rw [if_neg same]
    by_cases dis : Disjoint s t
    · rw [if_pos dis]
      have d : Disjoint (points edge s) (points edge t) := by
        rw [disjoint_iff_inter_eq_empty,points_common P edge apart sp tp,disjoint_iff_inter_eq_empty.mp dis]
        simp [points]
      simpa only [show ways 2*ways 2=100 by decide] using
        joint_local_bound X _ _ 2 2 (j-4) ((points_mono edge sp).trans inside) ((points_mono edge tp).trans inside)
          d (by omega) (by omega) (by omega)
    · rw [if_neg dis]
      apply Nat.le_zero.mpr (card_eq_zero.mpr (eq_empty_iff_forall_not_mem.mpr ?_))
      intro D hd
      have div := intersect_sealed (mem_inter.mp hd).1 (mem_inter.mp hd).2
      rw [points_common P edge apart sp tp,points_size P edge sz apart (inter_subset_left.trans sp)] at div
      have p : 0<(s∩t).card := card_pos.mpr (nonempty_iff_ne_empty.mpr (fun h => dis (disjoint_iff_inter_eq_empty.mpr h)))
      have bound := card_le_card (inter_subset_left : s∩t⊆s)
      have neq : (s∩t).card≠3 := by
        intro eq
        have l := eq_of_subset_of_card_le (inter_subset_left : s∩t⊆s) (by omega)
        have r := eq_of_subset_of_card_le (inter_subset_right : s∩t⊆t) (by omega)
        exact same (l.symm.trans r)
      omega
  have row (s) (hs : s∈S) : (∑ t∈S,if s=t then 0 else (E s∩E t).card) ≤
      (P.card-3).choose 3*(100*ways (j-4)) := by
    apply (sum_le_sum (fun t ht => pair s hs t ht)).trans
    rw [← sum_filter]
    have eq : S.filter (Disjoint s)=(P \ s).powersetCard 3 := by
      ext t
      simp only [S,mem_filter,mem_powersetCard]
      constructor
      · rintro ⟨⟨tp,tc⟩,d⟩
        exact ⟨fun x hx => mem_sdiff.mpr ⟨tp hx,fun xs => disjoint_left.mp d xs hx⟩,tc⟩
      · rintro ⟨tp,tc⟩
        exact ⟨⟨tp.trans sdiff_subset,tc⟩,disjoint_left.mpr (fun _ xs xt => (mem_sdiff.mp (tp xt)).2 xs)⟩
    rw [eq,sum_const,card_powersetCard,card_sdiff (mem_powersetCard.mp hs).1,(mem_powersetCard.mp hs).2]
    simp [nsmul_eq_mul]
  have all := sum_le_sum (s:=S) row
  have hit := two_term S E
  rw [sum_congr rfl each,sum_const] at hit
  simp only [S,card_powersetCard,nsmul_eq_mul,Nat.cast_id] at hit all
  change 2*(P.card.choose 3*(10*ways (j-2))) ≤ 2*(sixHits X P edge).card+_ at hit
  apply hit.trans (Nat.add_le_add_left _ _)
  simpa [S,Nat.mul_assoc] using all
end WildSieve
