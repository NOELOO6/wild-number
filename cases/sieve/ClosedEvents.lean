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

noncomputable def restrictedSeal {X : Finset V} (allowed : Finset (Layout X)) :=
  allowed.biUnion (fun M => occurs M.val)

theorem restricted_against (t : Nat) (total : Fintype.card V=3*t) (s : I → Finset V)
    (X : Finset V) (j : Nat) (size : X.card=3*j) (allowed : Finset (Layout X)) :
    Against s (fun i => sealEvent (s i)) X (restrictedSeal allowed)
      ((allowed.card : ℚ)*ways (t-j)/ways t) := by
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
  have one (M : Layout X) : ((occurs M.val ∩ A).card : ℚ) ≤ (ways (t-j) : ℚ)/ways t*A.card := by
    have ms := M.property.1.card_vertices
    rw [M.property.2,size] at ms
    have mj : M.val.card=j := by omega
    have bound := triple_lopsided t total sm M.val M.property.1 U (by simpa only [M.property.2] using dis)
    simpa only [avoid_eq,mj] using bound
  have sub : restrictedSeal allowed ∩ A ⊆ allowed.biUnion (fun M => occurs M.val ∩ A) := by
    intro D hD
    obtain ⟨e,a⟩ := mem_inter.mp hD
    obtain ⟨M,mk,occ⟩ := mem_biUnion.mp e
    exact mem_biUnion.mpr ⟨M,mk,mem_inter.mpr ⟨occ,a⟩⟩
  have card : ((restrictedSeal allowed ∩ A).card : ℚ) ≤ ∑ M∈allowed,((occurs M.val ∩ A).card : ℚ) := by
    exact_mod_cast (card_le_card sub).trans card_biUnion_le
  apply card.trans
  have b := sum_le_sum (s:=allowed) (fun M _ => one M)
  simpa [nsmul_eq_mul,div_eq_mul_inv,mul_assoc] using b

theorem seal_lopsided (t : Nat) (total : Fintype.card V=3*t) (s : I → Finset V)
    (X : Finset V) (j : Nat) (size : X.card=3*j) :
    Against s (fun i => sealEvent (s i)) X (sealEvent X) (sealWeight t j) := by
  classical
  have all : restrictedSeal (univ : Finset (Layout X)) = sealEvent X := by
    ext D
    simp only [restrictedSeal,mem_biUnion,mem_univ,true_and,mem_occurs,mem_seal]
  have bound := restricted_against t total s X j size (univ : Finset (Layout X))
  simpa only [all,card_univ,card_layout j X size,sealWeight] using bound

#print axioms seal_lopsided
end WildSieve
