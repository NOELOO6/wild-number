import LocalSeals
namespace WildSieve
open Finset
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The two subdivisions on opposite sides of a sealed set determine the
whole layout uniquely. -/
noncomputable def glueParts (X Y : Finset V) (sub : Y⊆X) :
    Layout Y × Layout (X \ Y) ↪ Layout X where
  toFun P := ⟨P.1.val∪P.2.val,P.1.property.1.combine P.2.property.1 (by
    rw [P.1.property.2,P.2.property.2];exact disjoint_sdiff),by
    rw [vertices_union,P.1.property.2,P.2.property.2,union_sdiff_of_subset sub]⟩
  inj' := by
    rintro ⟨a,b⟩ ⟨c,d⟩ eq
    have both : a.val∪b.val=c.val∪d.val := congrArg Subtype.val eq
    have incompatible (a : Layout Y) (b : Layout (X \ Y)) : Disjoint a.val b.val := by
      apply disjoint_left.mpr
      intro t ta tb
      obtain ⟨v,hv⟩ := card_pos.mp (by rw [a.property.1.size t ta];decide : 0<t.card)
      exact (mem_sdiff.mp (b.property.2 ▸ block_sub tb hv)).2 (a.property.2 ▸ block_sub ta hv)
    have aeq : a.val=c.val := by
      apply Subset.antisymm
      · intro t ht
        exact (mem_union.mp (both ▸ mem_union_left b.val ht)).resolve_right
          (fun h => disjoint_left.mp (incompatible a d) ht h)
      · intro t ht
        exact (mem_union.mp (both.symm ▸ mem_union_left d.val ht)).resolve_right
          (fun h => disjoint_left.mp (incompatible c b) ht h)
    have beq : b.val=d.val := by
      apply Subset.antisymm
      · intro t ht
        exact (mem_union.mp (both ▸ mem_union_right a.val ht)).resolve_left
          (fun h => disjoint_left.mp (incompatible c b) h ht)
      · intro t ht
        exact (mem_union.mp (both.symm ▸ mem_union_right c.val ht)).resolve_left
          (fun h => disjoint_left.mp (incompatible a d) h ht)
    exact Prod.ext (Subtype.ext aeq) (Subtype.ext beq)

theorem split_seal {X Y : Finset V} (sub : Y⊆X) {D : Layout X} (hit : D∈localSeal X Y) :
    ∃ P,glueParts X Y sub P=D := by
  obtain ⟨a,inc⟩ := local_seal_mem.mp hit
  let b : Layout (X \ Y) := ⟨D.val \ a.val,D.property.1.sub sdiff_subset,by
    rw [D.property.1.remove inc,D.property.2,a.property.2]⟩
  exact ⟨(a,b),Subtype.ext (union_sdiff_of_subset inc)⟩

theorem seal_glue_left (X Y Z : Finset V) (sub : Y⊆X) (P : Layout Y × Layout (X \ Y))
    (zy : Z⊆Y) : glueParts X Y sub P∈localSeal X Z ↔ P.1∈localSeal Y Z := by
  constructor
  · intro h
    obtain ⟨M,md⟩ := local_seal_mem.mp h
    refine local_seal_mem.mpr ⟨M,fun t ht => (mem_union.mp (md ht)).resolve_right (fun bad => ?_)⟩
    obtain ⟨v,hv⟩ := card_pos.mp (by rw [M.property.1.size t ht];decide : 0<t.card)
    exact (mem_sdiff.mp (P.2.property.2 ▸ block_sub bad hv)).2 (zy (M.property.2 ▸ block_sub ht hv))
  · intro h
    obtain ⟨M,md⟩ := local_seal_mem.mp h
    exact local_seal_mem.mpr ⟨M,md.trans subset_union_left⟩

theorem seal_glue_right (X Y Z : Finset V) (sub : Y⊆X) (P : Layout Y × Layout (X \ Y))
    (zy : Z⊆X \ Y) : glueParts X Y sub P∈localSeal X Z ↔ P.2∈localSeal (X \ Y) Z := by
  constructor
  · intro h
    obtain ⟨M,md⟩ := local_seal_mem.mp h
    refine local_seal_mem.mpr ⟨M,fun t ht => (mem_union.mp (md ht)).resolve_left (fun bad => ?_)⟩
    obtain ⟨v,hv⟩ := card_pos.mp (by rw [M.property.1.size t ht];decide : 0<t.card)
    exact (mem_sdiff.mp (zy (M.property.2 ▸ block_sub ht hv))).2 (P.1.property.2 ▸ block_sub bad hv)
  · intro h
    obtain ⟨M,md⟩ := local_seal_mem.mp h
    exact local_seal_mem.mpr ⟨M,md.trans subset_union_right⟩

/-- Count layouts with any condition that factors over a prescribed cut. -/
theorem split_card (X Y : Finset V) (sub : Y⊆X) (E : Finset (Layout X))
    (L : Finset (Layout Y)) (R : Finset (Layout (X \ Y))) (sealed : E⊆localSeal X Y)
    (law : ∀ P,glueParts X Y sub P∈E ↔ P.1∈L ∧ P.2∈R) : E.card=L.card*R.card := by
  classical
  have eq : E=(L×ˢR).map (glueParts X Y sub) := by
    ext D
    constructor
    · intro h
      obtain ⟨P,rfl⟩ := split_seal sub (sealed h)
      exact mem_map.mpr ⟨P,mem_product.mpr ((law P).mp h),rfl⟩
    · intro h
      obtain ⟨P,hp,rfl⟩ := mem_map.mp h
      exact (law P).mpr (mem_product.mp hp)
  rw [eq,card_map,card_product]

theorem split_upper (X Y : Finset V) (sub : Y⊆X) (E : Finset (Layout X))
    (L : Finset (Layout Y)) (R : Finset (Layout (X \ Y))) (sealed : E⊆localSeal X Y)
    (law : ∀ P,glueParts X Y sub P∈E → P.1∈L ∧ P.2∈R) : E.card≤L.card*R.card := by
  classical
  have incl : E⊆(L×ˢR).map (glueParts X Y sub) := by
    intro D h
    obtain ⟨P,rfl⟩ := split_seal sub (sealed h)
    exact mem_map.mpr ⟨P,mem_product.mpr (law P h),rfl⟩
  simpa using card_le_card incl

theorem seal_glue (X Y : Finset V) (sub : Y⊆X) (P : Layout Y × Layout (X \ Y)) :
    glueParts X Y sub P∈localSeal X Y := local_seal_mem.mpr ⟨P.1,subset_union_left⟩

theorem drop_cut (X Y : Finset V) (sub : Y⊆X) (E : Finset (Layout X)) (R : Finset (Layout (X \ Y)))
    (sealed : E⊆localSeal X Y) (law : ∀ P,glueParts X Y sub P∈E ↔ P.2∈R) :
    E.card=Fintype.card (Layout Y)*R.card := by
  simpa using split_card X Y sub E univ R sealed (fun P => by simpa using law P)

theorem equal_joint (X Y Z : Finset V) (a b c : Nat) (yx : Y⊆X) (zx : Z⊆X)
    (d : Disjoint Y Z) (ya : Y.card=3*a) (zb : Z.card=3*b) (rem : X.card-(Y.card+Z.card)=3*c) :
    (localSeal X Y∩localSeal X Z).card=ways a*ways b*ways c := by
  have zy : Z⊆X \ Y := fun v hv => mem_sdiff.mpr ⟨zx hv,fun hy => disjoint_left.mp d hy hv⟩
  rw [drop_cut X Y yx _ (localSeal (X \ Y) Z) inter_subset_left (fun P => by
    rw [mem_inter,seal_glue_right X Y Z yx P zy];simp [seal_glue]),card_layout a Y ya,
    local_seal_card (X \ Y) Z b c zy zb (by rw [card_sdiff yx];omega),Nat.mul_assoc]

/-- Both the intersection and the difference of two sealed regions are sealed. -/
theorem seal_parts {X Y Z : Finset V} {D : Layout X} (hy : D∈localSeal X Y) (hz : D∈localSeal X Z) :
    D∈localSeal X (Y∩Z) ∧ D∈localSeal X (Z \ Y) := by
  obtain ⟨P,p⟩ := local_seal_mem.mp hy
  obtain ⟨Q,q⟩ := local_seal_mem.mp hz
  have vi : vertices (P.val∩Q.val)=Y∩Z := by
    ext v
    constructor
    · rintro h
      obtain ⟨t,ht,vt⟩ := mem_biUnion.mp h
      exact mem_inter.mpr ⟨P.property.2 ▸ block_sub (mem_inter.mp ht).1 vt,Q.property.2 ▸ block_sub (mem_inter.mp ht).2 vt⟩
    · intro hv
      obtain ⟨a,ha,va⟩ := mem_biUnion.mp (P.property.2.symm ▸ (mem_inter.mp hv).1)
      obtain ⟨b,hb,vb⟩ := mem_biUnion.mp (Q.property.2.symm ▸ (mem_inter.mp hv).2)
      have eq := D.property.1.only (p ha) (q hb) va vb
      exact mem_biUnion.mpr ⟨a,mem_inter.mpr ⟨ha,eq.symm ▸ hb⟩,va⟩
  let M := P.val∩Q.val
  have ve : vertices (Q.val \ M)=Z \ Y := by
    rw [Q.property.1.remove (show M⊆Q.val from inter_subset_right),Q.property.2,show vertices M=Y∩Z from vi]
    ext v
    simp only [mem_sdiff,mem_inter];tauto
  exact ⟨local_seal_mem.mpr ⟨⟨M,P.property.1.sub inter_subset_left,vi⟩,inter_subset_left.trans p⟩,
    local_seal_mem.mpr ⟨⟨Q.val \ M,Q.property.1.sub sdiff_subset,ve⟩,sdiff_subset.trans q⟩⟩
end WildSieve
