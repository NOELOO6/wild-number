import TripleParts
namespace WildSieve
open Finset
variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem singleton_triple {b : Finset V} (size : b.card=3) : Triples ({b} : Blocks V) := by
  refine ⟨fun a ha => ?_,?_⟩
  · simpa [(mem_singleton.mp ha)] using size
  · intro a ha d hd ne
    exact False.elim (ne ((mem_singleton.mp ha).trans (mem_singleton.mp hd).symm))

omit [Fintype V] in
@[simp] theorem vertices_singleton (b : Finset V) : vertices ({b} : Blocks V)=b := by
  ext v
  simp [vertices]

private noncomputable def rootedEquiv (S : Finset V) (z : V) (hz : z ∈ S) :
    ((t : ↥((S.erase z).powersetCard 2)) × {D : Layout S // insert z t.val ∈ D.val}) ≃ Layout S := by
  classical
  let forget (a : (t : ↥((S.erase z).powersetCard 2)) × {D : Layout S // insert z t.val ∈ D.val}) := a.2.val
  refine Equiv.ofBijective forget ⟨?_,?_⟩
  · rintro ⟨a,L,ha⟩ ⟨b,K,hb⟩ same
    change L=K at same
    subst K
    have eq := L.property.1.only ha hb (mem_insert_self _ _) (mem_insert_self _ _)
    have az : z ∉ a.val := fun h => (mem_erase.mp ((mem_powersetCard.mp a.property).1 h)).1 rfl
    have bz : z ∉ b.val := fun h => (mem_erase.mp ((mem_powersetCard.mp b.property).1 h)).1 rfl
    have ab : a=b := Subtype.ext (by simpa [az,bz] using congrArg (fun x : Finset V => x.erase z) eq)
    subst b
    rfl
  · intro D
    obtain ⟨b,bd,zb⟩ := mem_biUnion.mp (show z ∈ vertices D.val by rwa [D.property.2])
    change z ∈ b at zb
    have bS : b ⊆ S := D.property.2 ▸ block_sub bd
    have size := D.property.1.size _ bd
    have valid : b.erase z ∈ (S.erase z).powersetCard 2 := mem_powersetCard.mpr
      ⟨erase_subset_erase z bS,by rw [card_erase_of_mem zb,size]⟩
    refine ⟨⟨⟨b.erase z,valid⟩,D,?_⟩,rfl⟩
    simpa [insert_erase zb] using bd

theorem card_layout (k : Nat) (S : Finset V) (size : S.card=3*k) :
    Fintype.card (Layout S) = ways k := by
  classical
  induction k generalizing S with
  | zero =>
    have sz : S=∅ := card_eq_zero.mp (by omega)
    subst S
    let D : Layout (∅ : Finset V) := ⟨∅,⟨by simp,by simp⟩,by simp [vertices]⟩
    apply Fintype.card_eq_one_iff.mpr
    refine ⟨D,?_⟩
    intro K
    apply Subtype.ext
    have n := K.property.1.card_vertices
    rw [K.property.2,card_empty] at n
    exact card_eq_zero.mp (by omega)
  | succ k ih =>
    obtain ⟨z,hz⟩ := card_pos.mp (show 0<S.card by omega)
    let T := ↥((S.erase z).powersetCard 2)
    have each (t : T) : Fintype.card {D : Layout S // insert z t.val ∈ D.val}=ways k := by
      obtain ⟨sub,tsize⟩ := mem_powersetCard.mp t.property
      let b := insert z t.val
      have nz : z ∉ t.val := fun h => (mem_erase.mp (sub h)).1 rfl
      have bsize : b.card=3 := by simp [b,nz,tsize]
      have inside : b ⊆ S := insert_subset hz (sub.trans (erase_subset _ _))
      let M : Blocks V := {b}
      have vm : vertices M=b := vertices_singleton _
      have one := completeEquiv S M (singleton_triple bsize) (vm ▸ inside)
      let eq : {D : Layout S // b ∈ D.val} ≃ {D : Layout S // M ⊆ D.val} :=
        Equiv.subtypeEquivRight (fun _ => by simp [M])
      have left := Fintype.card_congr (eq.trans one)
      change Fintype.card {D : Layout S // b ∈ D.val} = _
      apply left.trans
      apply ih
      rw [vm,card_sdiff inside,bsize]
      omega
    rw [← Fintype.card_congr (rootedEquiv S z hz),Fintype.card_sigma]
    calc
      _ = ∑ _ : T,ways k := sum_congr rfl (fun t _ => each t)
      _ = _ := by simp [T,ways,← Nat.choose_eq_fast_choose,card_erase_of_mem hz,size,Nat.mul_succ]

end WildSieve
