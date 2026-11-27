import Coupling
import Relabel
namespace WildSieve
open Finset
variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I]

def stays (D : Blocks V) (W : Finset V) := D.filter fun b => b ⊆ W

omit [Fintype V] in
private theorem preserves {W : Finset V} (g : Equiv.Perm V) (fixW : g.finsetCongr W=W)
    (D Q : Blocks V) : stays D W ⊆ Q ↔ stays (rename g D) W ⊆ rename g Q := by
  have inside (b : Finset V) : g.finsetCongr b ⊆ W ↔ b ⊆ W := by
    conv_lhs => rhs; rw [← fixW]
    exact Finset.map_subset_map
  constructor
  · intro sub b hb
    obtain ⟨a,rfl⟩ := g.finsetCongr.surjective b
    obtain ⟨aD,aW⟩ := mem_filter.mp hb
    exact (rename_mem _ _ _).mpr (sub (mem_filter.mpr ⟨(rename_mem _ _ _).mp aD,(inside _).mp aW⟩))
  · intro sub b hb
    obtain ⟨bd,bW⟩ := mem_filter.mp hb
    exact (rename_mem g Q b).mp (sub (mem_filter.mpr ⟨(rename_mem _ _ _).mpr bd,(inside _).mpr bW⟩))

private theorem fills (W : Finset V) (w : Nat) (size : W.card=3*w) (D : Layout (univ : Finset V)) :
    ∃ Q : Layout W, stays D.val W ⊆ Q.val := by
  let A := stays D.val W
  have valid : Triples A := D.property.1.sub (filter_subset _ _)
  have sub : vertices A ⊆ W := by
    intro x hx
    obtain ⟨b,hb,xb⟩ := mem_biUnion.mp hx
    exact (mem_filter.mp hb).2 xb
  have sz : (W \ vertices A).card=3*(w-A.card) := by
    rw [card_sdiff sub,size,valid.card_vertices,Nat.mul_sub]
  have nonempty := Fintype.card_pos_iff.mp ((card_layout _ _ sz).symm ▸ ways_pos (w-A.card))
  obtain ⟨F⟩ := nonempty
  have dis : Disjoint (vertices A) (vertices F.val) := by rw [F.property.2]; exact disjoint_sdiff
  exact ⟨⟨A ∪ F.val,valid.combine F.property.1 dis,by rw [vertices_union,F.property.2,union_sdiff_of_subset sub]⟩,
    subset_union_left⟩

noncomputable def occurs (M : Blocks V) : Finset (Layout (univ : Finset V)) := by
  classical
  exact univ.filter fun D => M ⊆ D.val

theorem mem_occurs {M : Blocks V} {D : Layout (univ : Finset V)} : D ∈ occurs M ↔ M ⊆ D.val := by
  simp [occurs]

/-- Canonical events for a uniformly chosen triple partition satisfy the
lopsided inequality, with their exact probabilities. -/
theorem triple_lopsided (t : Nat) (total : Fintype.card V = 3*t) (short : I → Blocks V)
    (M : Blocks V) (valid : Triples M) :
    Against (fun i => vertices (short i)) (fun i => occurs (short i)) (vertices M)
      (occurs M) ((ways (t-M.card) : ℚ) / ways t) := by
  classical
  intro U dis
  let full : Finset V := univ
  let W := full \ vertices M
  let s (i : I) := vertices (short i)
  let A := avoid s (fun i => occurs (short i)) U
  let B := (univ : Finset (Layout W)).filter fun Q => ∀ i, s i ⊆ U → ¬short i ⊆ Q.val
  have fullSize : full.card=3*t := by simpa [full] using total
  have wSize : W.card=3*(t-M.card) := by
    rw [show W=full \ vertices M from rfl,card_sdiff (subset_univ _),fullSize,valid.card_vertices,Nat.mul_sub]
  have cardL := card_layout _ full fullSize
  have cardR := card_layout _ W wSize
  letI : Nonempty (Layout W) := Fintype.card_pos_iff.mp (cardR.symm ▸ ways_pos _)
  let rel (D : Layout full) (Q : Layout W) := stays D.val W ⊆ Q.val
  have symmetry (y z : Layout W) : ∃ (f : Equiv.Perm (Layout full)) (g : Equiv.Perm (Layout W)),
      g y=z ∧ ∀ D Q, rel D Q ↔ rel (f D) (g Q) := by
    obtain ⟨e,fixW,renameEq,_⟩ := transitive_layout W y z
    have fixFull : e.finsetCongr full=full := by ext x; simp [full,Equiv.finsetCongr_apply]
    exact ⟨layoutPerm e fixFull,layoutPerm e fixW,Subtype.ext renameEq,fun D Q => preserves e fixW D.val Q.val⟩
  have keeps (D : Layout full) (Q : Layout W) (h : rel D Q) (hq : Q ∈ B) : D ∈ A := by
    apply mem_avoid.mpr
    intro i su ein
    apply (mem_filter.mp hq).2 i su
    intro b bi
    apply h (mem_filter.mpr ⟨mem_occurs.mp ein bi,?_⟩)
    intro x xb
    apply mem_sdiff.mpr
    have xu := su (block_sub bi xb)
    exact ⟨mem_univ _,fun xm => disjoint_left.mp dis xm xu⟩
  have inequality := uniform_coupling rel (fills W _ wSize) symmetry A B keeps
  have inj : (occurs M ∩ A).card ≤ B.card := by
    apply card_le_card_of_injOn (fun D : Layout full =>
      if h : M ⊆ D.val then (completeEquiv full M valid (subset_univ _)) ⟨D,h⟩
      else Classical.choice ‹Nonempty (Layout W)›)
    · intro D hD
      obtain ⟨occ,good⟩ := mem_inter.mp hD
      rw [dif_pos (mem_occurs.mp occ)]
      apply mem_filter.mpr
      refine ⟨mem_univ _,fun i su h => mem_avoid.mp good i su (mem_occurs.mpr ?_)⟩
      exact h.trans sdiff_subset
    · intro D hD K hK eq
      have d := mem_occurs.mp (mem_inter.mp hD).1
      have k := mem_occurs.mp (mem_inter.mp hK).1
      simp only [dif_pos d,dif_pos k] at eq
      exact congrArg Subtype.val ((completeEquiv full M valid (subset_univ _)).injective eq)
  have imass : ((occurs M ∩ A).card : ℚ) ≤ B.card := by exact_mod_cast inj
  rw [cardL,cardR] at inequality
  change ((occurs M ∩ A).card : ℚ) ≤ _
  have pt : 0 < (ways t : ℚ) := by exact_mod_cast ways_pos t
  rw [div_mul_eq_mul_div,le_div_iff₀ pt]
  exact (mul_le_mul_of_nonneg_right imass pt.le).trans (by simpa [mul_comm] using inequality)

#print axioms triple_lopsided
end WildSieve
