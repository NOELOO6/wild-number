import Factors

namespace WildSieve.TwoTripleCuts
open Finset
variable {V C : Type} [LinearOrder V]

def jointlyClosed (F : Factor V C) (c d : C) (S : Finset V) :=
  Closed (F.f c) S ∧ Closed (F.f d) S

private theorem no_pair (F : Factor V C) {c d : C} (different : c≠d) {S : Finset V}
    (closed : jointlyClosed F c d S) : S.card≠2 := by
  intro size
  obtain ⟨a,b,ab,rfl⟩ := card_eq_two.mp size
  have mate (i : C) (cl : Closed (F.f i) {a,b}) : F.f i a=b := by
    have inside := cl a (mem_insert_self _ _)
    simp only [mem_insert,mem_singleton] at inside
    exact inside.resolve_left (F.moving i a).symm
  exact different (F.unique a ((mate c closed.1).trans (mate d closed.2).symm))

private theorem diff_closed (F : Factor V C) (i : C) {S T : Finset V}
    (s : Closed (F.f i) S) (t : Closed (F.f i) T) : Closed (F.f i) (S \ T) := by
  intro x hx
  obtain ⟨xs,xt⟩ := mem_sdiff.mp hx
  exact mem_sdiff.mpr ⟨s x xs,fun h => xt (F.invol i x ▸ t _ h)⟩

/-- Distinct common six-sets of two colors are disjoint. A nontrivial
intersection would leave a two-point set closed by both perfect matchings. -/
theorem common_sixes_disjoint (F : Factor V C) {c d : C} (different : c≠d)
    {S T : Finset V} (s : jointlyClosed F c d S) (t : jointlyClosed F c d T)
    (ss : S.card=6) (ts : T.card=6) (ne : S≠T) : Disjoint S T := by
  let U := S∩T
  have joint : jointlyClosed F c d U :=
    ⟨fun x hx => mem_inter.mpr ⟨s.1 _ (mem_inter.mp hx).1,t.1 _ (mem_inter.mp hx).2⟩,
     fun x hx => mem_inter.mpr ⟨s.2 _ (mem_inter.mp hx).1,t.2 _ (mem_inter.mp hx).2⟩⟩
  have rest : jointlyClosed F c d (S \ U) :=
    ⟨diff_closed F c s.1 joint.1,diff_closed F d s.2 joint.2⟩
  have even := closed_size (F.invol c) (F.moving c) joint.1
  have m1 := no_pair F different joint
  have m2 := no_pair F different rest
  have sub : U⊆S := inter_subset_left
  rw [card_sdiff sub,ss] at m2
  have bound := (card_le_card sub).trans_eq ss
  have full : U.card≠6 := by
    intro size
    have eqS : U=S := eq_of_subset_of_card_le sub (by omega)
    have eqT : U=T := eq_of_subset_of_card_le inter_subset_right (by omega)
    exact ne (eqS.symm.trans eqT)
  have zero : U.card=0 := by omega
  exact disjoint_iff_inter_eq_empty.mpr (card_eq_zero.mp zero)

/-- In order 6s+4, attaining s common ordinary six-sets forces the four
remaining vertices, including the distinguished root, to close in both colors. -/
theorem packing_forces_four [Fintype V] (F : Factor V C) {c d : C} (ne : c≠d)
    (r : V) (K : Finset (Finset V)) (s : Nat) (order : Fintype.card V=6*s+4)
    (six : ∀ S∈K,S.card=6 ∧ r∉S ∧ jointlyClosed F c d S) :
    K.card≤s ∧ (K.card=s → ∃ Q : Finset V,r∈Q ∧ Q.card=4 ∧ jointlyClosed F c d Q) := by
  classical
  let U := K.biUnion id
  have dis : (K : Set (Finset V)).PairwiseDisjoint id := fun S hs T ht dif =>
    common_sixes_disjoint F ne (six _ hs).2.2 (six _ ht).2.2 (six _ hs).1 (six _ ht).1 dif
  have size : U.card=6*K.card := by
    rw [show U=K.biUnion id from rfl,card_biUnion dis]
    simp only [id_eq,sum_congr rfl (fun S hs => (six S hs).1),sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_comm]
  have cap := card_le_univ U
  have rr : r∉U := by
    intro h
    obtain ⟨S,hs,rs⟩ := mem_biUnion.mp h
    exact (six _ hs).2.1 rs
  have closed (i : C) (each : ∀ S∈K,Closed (F.f i) S) : Closed (F.f i) (univ \ U) := by
    apply diff_closed F i (fun _ _ => mem_univ _) _
    intro x hx
    obtain ⟨S,hs,xs⟩ := mem_biUnion.mp hx
    exact mem_biUnion.mpr ⟨S,hs,each S hs x xs⟩
  refine ⟨by omega,?_⟩
  intro full
  refine ⟨univ \ U,mem_sdiff.mpr ⟨mem_univ _,rr⟩,?_,
    closed c (fun S h => (six S h).2.2.1),closed d (fun S h => (six S h).2.2.2)⟩
  rw [card_sdiff (subset_univ _),card_univ,order,size,full]
  omega

#print axioms common_sixes_disjoint
#print axioms packing_forces_four
end WildSieve.TwoTripleCuts
