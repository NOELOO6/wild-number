import TripleCoupling
namespace WildSieve
open Finset
variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I]

/-- The indicated set is a union of entire triples of the layout. -/
noncomputable def sealEvent (S : Finset V) : Finset (Layout (univ : Finset V)) := by
  classical
  exact univ.filter fun D => ∃ M : Layout S, M.val ⊆ D.val

theorem mem_seal {S : Finset V} {D : Layout (univ : Finset V)} :
    D ∈ sealEvent S ↔ ∃ M : Layout S, M.val ⊆ D.val := by classical simp [sealEvent]

def sealWeight (t j : Nat) : ℚ := (ways j : ℚ) * ways (t-j) / ways t

theorem seal_lopsided (t : Nat) (total : Fintype.card V=3*t) (s : I → Finset V)
    (X : Finset V) (j : Nat) (size : X.card=3*j) :
    Against s (fun i => sealEvent (s i)) X (sealEvent X) (sealWeight t j) := by
  classical
  let K := (i : I) × Layout (s i)
  let sm (k : K) := k.2.val
  have avoid_eq (U : Finset V) : avoid (fun k => vertices (sm k)) (fun k => occurs (sm k)) U =
      avoid s (fun i => sealEvent (s i)) U := by
    ext D
    rw [mem_avoid,mem_avoid]
    constructor
    · intro all i h ei
      obtain ⟨M,hm⟩ := mem_seal.mp ei
      exact all ⟨i,M⟩ (M.property.2 ▸ h) (mem_occurs.mpr hm)
    · intro all k h ei
      exact all k.1 (k.2.property.2 ▸ h) (mem_seal.mpr ⟨k.2,mem_occurs.mp ei⟩)
  intro U dis
  let A := avoid s (fun i => sealEvent (s i)) U
  have one (M : Layout X) : ((occurs M.val ∩ A).card : ℚ) ≤
      (ways (t-j) : ℚ) / ways t * A.card := by
    have ms := M.property.1.card_vertices
    rw [M.property.2,size] at ms
    have mj : M.val.card=j := by omega
    have bound := triple_lopsided t total sm M.val M.property.1 U (by simpa only [M.property.2] using dis)
    simpa only [avoid_eq,mj] using bound
  have cover : sealEvent X ∩ A ⊆ univ.biUnion (fun M : Layout X => occurs M.val ∩ A) := by
    intro D hD
    obtain ⟨sealed,ha⟩ := mem_inter.mp hD
    obtain ⟨M,hm⟩ := mem_seal.mp sealed
    exact mem_biUnion.mpr ⟨M,mem_univ _,mem_inter.mpr ⟨mem_occurs.mpr hm,ha⟩⟩
  have count : ((sealEvent X ∩ A).card : ℚ) ≤ ∑ M : Layout X, ((occurs M.val ∩ A).card : ℚ) := by
    exact_mod_cast (card_le_card cover).trans card_biUnion_le
  apply count.trans
  have b := Finset.sum_le_sum (s := (univ : Finset (Layout X))) (fun M _ => one M)
  simpa [sealWeight,card_layout j X size,nsmul_eq_mul,div_eq_mul_inv,mul_assoc] using b

#print axioms seal_lopsided
end WildSieve
