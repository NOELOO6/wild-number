import TripleCounts
namespace WildSieve
open Finset
variable {V : Type} [DecidableEq V]

def rename (e : Equiv.Perm V) (D : Blocks V) := e.finsetCongr.finsetCongr D

omit [DecidableEq V] in
theorem rename_mem (e : Equiv.Perm V) (D : Blocks V) (b : Finset V) :
    e.finsetCongr b ∈ rename e D ↔ b ∈ D := by
  change e.finsetCongr.toEmbedding b ∈ D.map e.finsetCongr.toEmbedding ↔ _
  exact Finset.mem_map' _

omit [DecidableEq V] in
theorem at_rename (e : Equiv.Perm V) (s : Finset V) (x : V) :
    e x ∈ e.finsetCongr s ↔ x ∈ s := by simp [Equiv.finsetCongr_apply]

theorem vertices_rename (e : Equiv.Perm V) (D : Blocks V) :
    vertices (rename e D) = e.finsetCongr (vertices D) := by
  ext y
  obtain ⟨x,rfl⟩ := e.surjective y
  rw [at_rename]
  constructor
  · intro hx
    obtain ⟨b,hb,xb⟩ := mem_biUnion.mp hx
    obtain ⟨a,rfl⟩ := e.finsetCongr.surjective b
    exact mem_biUnion.mpr ⟨a,(rename_mem e D a).mp hb,(at_rename e a x).mp xb⟩
  · intro hx
    obtain ⟨a,ha,xa⟩ := mem_biUnion.mp hx
    exact mem_biUnion.mpr ⟨e.finsetCongr a,(rename_mem e D a).mpr ha,(at_rename e a x).mpr xa⟩

omit [DecidableEq V] in
theorem Triples.renamed {D : Blocks V} (h : Triples D) (e : Equiv.Perm V) : Triples (rename e D) := by
  refine ⟨?_,?_⟩
  · intro b hb
    obtain ⟨a,rfl⟩ := e.finsetCongr.surjective b
    simpa [Equiv.finsetCongr_apply] using h.size _ ((rename_mem _ _ _).mp hb)
  · intro a ha b hb ne
    obtain ⟨u,rfl⟩ := e.finsetCongr.surjective a
    obtain ⟨v,rfl⟩ := e.finsetCongr.surjective b
    apply disjoint_left.mpr
    intro x xa xb
    obtain ⟨y,rfl⟩ := e.surjective x
    exact disjoint_left.mp (h.separate _ ((rename_mem _ _ _).mp ha) _ ((rename_mem _ _ _).mp hb)
      (fun eq => ne (congrArg e.finsetCongr eq))) ((at_rename _ _ _).mp xa) ((at_rename _ _ _).mp xb)

omit [DecidableEq V] in
private theorem back_rename (e : Equiv.Perm V) (D : Blocks V) : rename e.symm (rename e D)=D := by
  change e.finsetCongr.finsetCongr.symm (e.finsetCongr.finsetCongr D)=D
  exact e.finsetCongr.finsetCongr.symm_apply_apply D

def layoutPerm {S : Finset V} (e : Equiv.Perm V) (fixes : e.finsetCongr S=S) : Equiv.Perm (Layout S) where
  toFun := fun D => ⟨rename e D.val,D.property.1.renamed e,by rw [vertices_rename,D.property.2,fixes]⟩
  invFun := fun D => ⟨rename e.symm D.val,D.property.1.renamed _,by
    rw [vertices_rename,D.property.2]
    exact e.finsetCongr.symm_apply_eq.mpr fixes.symm⟩
  left_inv D := Subtype.ext (back_rename e D.val)
  right_inv D := Subtype.ext (back_rename e.symm D.val)

private noncomputable def labelPoints {S : Finset V} (D : Layout S) :
    ((b : ↥D.val) × ↥b.val) ≃ ↥S := by
  let f (b : (b : ↥D.val) × ↥b.val) : ↥S :=
    ⟨b.2.val,by simpa only [D.property.2] using block_sub b.1.property b.2.property⟩
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · rintro ⟨a,x⟩ ⟨b,y⟩ eq
    have xy : x.val=y.val := congrArg Subtype.val eq
    have ab : a=b := Subtype.ext (D.property.1.only a.property b.property x.property (xy ▸ y.property))
    subst b
    exact congrArg (Sigma.mk a) (Subtype.ext xy)
  · intro x
    obtain ⟨a,ha,xa⟩ := mem_biUnion.mp (show x.val ∈ vertices D.val from D.property.2.symm ▸ x.property)
    exact ⟨⟨⟨a,ha⟩,⟨x.val,xa⟩⟩,rfl⟩

/-- Any two layouts of S are related by a permutation fixing every point
outside S. The construction first matches blocks, then points within blocks. -/
theorem transitive_layout (S : Finset V) (D K : Layout S) :
    ∃ e : Equiv.Perm V, e.finsetCongr S=S ∧ rename e D.val=K.val ∧ ∀ x ∉ S, e x=x := by
  classical
  have d := D.property.1.card_vertices
  have k := K.property.1.card_vertices
  rw [D.property.2] at d
  rw [K.property.2] at k
  let blocks : ↥D.val ≃ ↥K.val := Finset.equivOfCardEq (by omega)
  let pts (b : ↥D.val) : ↥b.val ≃ ↥(blocks b).val := Finset.equivOfCardEq
    ((D.property.1.size _ b.property).trans (K.property.1.size _ (blocks b).property).symm)
  let matchPts : ((b : ↥D.val) × ↥b.val) ≃ ((b : ↥K.val) × ↥b.val) := Equiv.sigmaCongr blocks pts
  let inside := ((labelPoints D).symm.trans matchPts).trans (labelPoints K)
  let e := Equiv.Perm.ofSubtype inside
  have insideAt (b : ↥D.val) (x : ↥b.val) : e x.val = (pts b x).val := by
    have eq := Equiv.Perm.ofSubtype_apply_coe inside (labelPoints D ⟨b,x⟩)
    change e ((labelPoints D) ⟨b,x⟩).val = _
    rw [eq]
    change (((labelPoints K) (matchPts ((labelPoints D).symm (labelPoints D ⟨b,x⟩)))).val) = _
    rw [Equiv.symm_apply_apply]
    rfl
  have perBlock (b : ↥D.val) : e.finsetCongr b.val=(blocks b).val := by
    apply eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨x,hx,rfl⟩ := mem_map.mp hy
      exact insideAt b ⟨x,hx⟩ ▸ (pts b ⟨x,hx⟩).property
    · simp only [Equiv.finsetCongr_apply,card_map,D.property.1.size _ b.property,K.property.1.size _ (blocks b).property,le_refl]
  have renamed : rename e D.val=K.val := by
    ext b
    constructor
    · intro hb
      obtain ⟨a,ha,rfl⟩ := mem_map.mp hb
      exact perBlock ⟨a,ha⟩ ▸ (blocks ⟨a,ha⟩).property
    · intro hb
      obtain ⟨a,eq⟩ := blocks.surjective ⟨b,hb⟩
      have pair := (perBlock a).trans (congrArg Subtype.val eq)
      change e.finsetCongr a.val=b at pair
      rw [← pair]
      exact (rename_mem e D.val a.val).mpr a.property
  refine ⟨e,?_,renamed,fun x hx => Equiv.Perm.ofSubtype_apply_of_not_mem inside hx⟩
  rw [← D.property.2,← vertices_rename,renamed,K.property.2,D.property.2]

end WildSieve
