import Mathlib.GroupTheory.Perm.ViaEmbedding
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import MatchingModel

namespace WildExact.TripleRepair
open Finset
abbrev Slot := Fin 3
abbrev Layout (m : Nat) (V : Type) := (Fin m × Slot) ≃ V

/-- A transpose of three rows, with a cyclic offset in the third source row. -/
private def transpose (k : Slot) : Equiv.Perm (Slot × Slot) where
  toFun p := (p.2, if p.2=2 then p.1+k else p.1)
  invFun p := (if p.1=2 then p.2-k else p.2,p.1)
  left_inv := by rintro ⟨i,j⟩; by_cases h : j=2 <;> simp [h]
  right_inv := by rintro ⟨i,j⟩; by_cases h : i=2 <;> simp [h]

variable {m : Nat} {V : Type} [Fintype V]
private def rowMap (a b c : Fin m) : Slot → Fin m := fun i => if i=0 then a else if i=1 then b else c

private theorem row_inj {a b c : Fin m} (ab : a≠b) (ca : c≠a) (cb : c≠b) :
    Function.Injective (rowMap a b c) := by
  intro i j h
  have tri : ∀ z : Slot, z=0 ∨ z=1 ∨ z=2 := by decide
  rcases tri i with rfl|rfl|rfl <;> rcases tri j with rfl|rfl|rfl <;> simp_all [rowMap,eq_comm]

/-- For each fixed pair at most d vertices are forbidden. There are
3(m−2) choices of a third row and a rotation. Each forbidden completion
spoils at most one choice for its position in the pair of source rows. -/
private theorem third_row (bad : V → V → V → Prop) [∀ x y z, Decidable (bad x y z)]
    (d : Nat) (cap : ∀ x y, x≠y → (univ.filter (bad x y)).card≤d)
    (large : d+2<m) (L : Layout m V) (a b : Fin m) (ab : a≠b) :
    ∃ c : Fin m, c≠a ∧ c≠b ∧ ∃ k : Slot, ∀ i : Slot,
      ¬bad (L (a,i)) (L (b,i)) (L (c,i+k)) := by
  classical
  let rest := ((univ : Finset (Fin m)).erase a).erase b
  let stop (i : Slot) := univ.filter (bad (L (a,i)) (L (b,i)))
  have per (i : Slot) : (stop i).card≤d := cap _ _ (fun h => ab (Prod.mk.inj (L.injective h)).1)
  by_contra! none
  have obstruct (p : ↥rest × Slot) : ∃ i : Slot, L (p.1.val,i+p.2)∈stop i := by
    obtain ⟨cb,h⟩ := mem_erase.mp p.1.property
    obtain ⟨i,blocked⟩ := none p.1.val (mem_erase.mp h).1 cb p.2
    exact ⟨i,mem_filter.mpr ⟨mem_univ _,blocked⟩⟩
  choose pos hit using obstruct
  let key (p : ↥rest × Slot) : (i : Slot) × ↥(stop i) :=
    ⟨pos p,L (p.1.val,pos p+p.2),hit p⟩
  have inj : Function.Injective key := by
    intro p q eq
    have same : pos p=pos q := congrArg Sigma.fst eq
    have vert := congrArg (fun z : (i : Slot) × ↥(stop i) => z.2.val) eq
    change L (p.1.val,pos p+p.2)=L (q.1.val,pos q+q.2) at vert
    rw [same] at vert
    obtain ⟨v,k⟩ := Prod.mk.inj (L.injective vert)
    exact Prod.ext (Subtype.ext v) (add_left_cancel k)
  have le := Fintype.card_le_of_injective key inj
  rw [Fintype.card_prod,Fintype.card_sigma,Fintype.card_coe,Fintype.card_fin] at le
  have count : rest.card=m-1-1 := by
    simp [rest,card_erase_of_mem,ab.symm]
  have upper := sum_le_sum (s:=(univ : Finset Slot)) (fun i _ => per i)
  simp only [Fintype.card_coe] at le
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at upper
  omega

private def GoodRow (bad : V → V → V → Prop) (L : Layout m V) (r : Fin m) :=
  ¬bad (L (r,0)) (L (r,1)) (L (r,2))

/-- For any forbidden family of triples of pair degree at most d, a
partition into m ≥ d+3 admissible triples exists. A single repair changes
only three rows, including any specified bad row. -/
theorem partition {bad : V → V → V → Prop}
    [dec : ∀ x y z, Decidable (bad x y z)]
    (d : Nat) (cap : ∀ x y, x≠y → (univ.filter (bad x y)).card≤d)
    (large : d+2<m) (start : Layout m V) :
    ∃ L : Layout m V, ∀ r, ¬bad (L (r,0)) (L (r,1)) (L (r,2)) := by
  classical
  let fails (L : Layout m V) := univ.filter (fun r => ¬GoodRow bad L r)
  obtain ⟨L,_,least⟩ := exists_min_image (univ : Finset (Layout m V)) (fun L => (fails L).card)
    ⟨start,mem_univ _⟩
  refine ⟨L,?_⟩
  intro a
  by_contra h
  obtain ⟨b,ab⟩ : ∃ b : Fin m, a≠b := by
    let b₀ : Fin m := ⟨0,by omega⟩
    let b₁ : Fin m := ⟨1,by omega⟩
    by_cases eq : a=b₀
    · exact ⟨b₁,by rw [eq]; exact fun h => Nat.zero_ne_one (congrArg Fin.val h)⟩
    · exact ⟨b₀,eq⟩
  obtain ⟨c,ca,cb,k,clear⟩ := third_row bad d cap large L a b ab
  let R := rowMap a b c
  let emb : Slot × Slot ↪ Fin m × Slot :=
    (⟨R,row_inj ab ca cb⟩ : Slot ↪ Fin m).prodMap (Function.Embedding.refl Slot)
  let perm := (transpose k).viaEmbedding emb
  let M : Layout m V := perm.trans L
  have selected (i : Slot) : GoodRow bad M (R i) := by
    have mv (j : Slot) : M (R i,j)=L (emb (transpose k (i,j))) := by
      change L ((transpose k).viaEmbedding emb (emb (i,j)))=_
      rw [Equiv.Perm.viaEmbedding_apply]
    simp only [GoodRow,mv]
    simpa [emb,transpose,R,rowMap] using clear i
  have fixed (r : Fin m) (out : r∉Set.range R) (j : Slot) : M (r,j)=L (r,j) := by
    change L ((transpose k).viaEmbedding emb (r,j))=_
    rw [Equiv.Perm.viaEmbedding_apply_of_not_mem]
    rintro ⟨⟨i,s⟩,e⟩
    exact out ⟨i,congrArg Prod.fst e⟩
  have sub : fails M ⊆ (fails L).erase a := by
    intro r hr
    have no := (mem_filter.mp hr).2
    have outside : r∉Set.range R := by rintro ⟨i,rfl⟩; exact no (selected i)
    refine mem_erase.mpr ⟨fun eq => outside ⟨0,eq.symm⟩,mem_filter.mpr ⟨mem_univ _,?_⟩⟩
    simpa [GoodRow,fixed r outside] using no
  have old : a∈fails L := mem_filter.mpr ⟨mem_univ _,fun good => good h⟩
  exact (Nat.not_lt_of_ge (least M (mem_univ _)))
    ((card_le_card sub).trans_lt (card_lt_card (erase_ssubset old)))

end WildExact.TripleRepair
