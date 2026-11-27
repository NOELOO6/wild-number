import InnerCuts
namespace WildSieve
open Finset
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Layouts of X that group the points of Y entirely within Y. -/
noncomputable def localSeal (X Y : Finset V) : Finset (Layout X) := by
  classical exact univ.filter fun D => ∃ M : Layout Y,M.val⊆D.val

theorem local_seal_mem {X Y : Finset V} {D : Layout X} :
    D∈localSeal X Y ↔ ∃ M : Layout Y,M.val⊆D.val := by classical simp [localSeal]

omit [Fintype V] in
private theorem same_subdivision {X Y : Finset V} {D : Layout X} {P Q : Layout Y}
    (p : P.val⊆D.val) (q : Q.val⊆D.val) : P=Q := by
  have incl (P Q : Layout Y) (p : P.val⊆D.val) (q : Q.val⊆D.val) : P.val⊆Q.val := by
    intro b hb
    obtain ⟨v,hv⟩ := card_pos.mp (show 0<b.card by rw [P.property.1.size b hb]; decide)
    have atQ : v∈vertices Q.val := Q.property.2.symm ▸ P.property.2 ▸ block_sub hb hv
    obtain ⟨a,ha,va⟩ := mem_biUnion.mp atQ
    exact (D.property.1.only (p hb) (q ha) hv va).symm ▸ ha
  exact Subtype.ext (Subset.antisymm (incl P Q p q) (incl Q P q p))

theorem local_seal_card (X Y : Finset V) (a b : Nat) (sub : Y⊆X)
    (one : Y.card=3*a) (two : X.card-Y.card=3*b) : (localSeal X Y).card=ways a*ways b := by
  classical
  let E (M : Layout Y) := extensions X M.val
  have eq : localSeal X Y=univ.biUnion E := by ext D; simp [localSeal,E,extensions]
  have dis : ((univ : Finset (Layout Y)) : Set (Layout Y)).PairwiseDisjoint E := by
    intro M _ N _ ne
    exact disjoint_left.mpr fun _ hm hn => ne (same_subdivision (mem_filter.mp hm).2 (mem_filter.mp hn).2)
  have each (M : Layout Y) : (E M).card=ways b :=
    extension_card X M.val M.property.1 (M.property.2.symm ▸ sub) b (by rw [M.property.2,two])
  rw [eq,card_biUnion dis]
  simp only [each,sum_const,card_univ,card_layout a Y one,nsmul_eq_mul,Nat.cast_id]

/-- The intersection of two sealed regions is again a union of whole triples. -/
theorem intersect_sealed {X Y Z : Finset V} {D : Layout X}
    (p : D∈localSeal X Y) (q : D∈localSeal X Z) : 3 ∣ (Y∩Z).card := by
  classical
  obtain ⟨P,pd⟩ := local_seal_mem.mp p
  obtain ⟨Q,qd⟩ := local_seal_mem.mp q
  have eq : vertices (P.val∩Q.val)=Y∩Z := by
    ext v
    constructor
    · intro hv
      obtain ⟨b,hb,vb⟩ := mem_biUnion.mp hv
      exact mem_inter.mpr ⟨P.property.2 ▸ block_sub (mem_inter.mp hb).1 vb,Q.property.2 ▸ block_sub (mem_inter.mp hb).2 vb⟩
    · intro hv
      obtain ⟨y,z⟩ := mem_inter.mp hv
      obtain ⟨a,ha,va⟩ := mem_biUnion.mp (P.property.2.symm ▸ y)
      obtain ⟨b,hb,vb⟩ := mem_biUnion.mp (Q.property.2.symm ▸ z)
      have ab := D.property.1.only (pd ha) (qd hb) va vb
      exact mem_biUnion.mpr ⟨a,mem_inter.mpr ⟨ha,ab.symm ▸ hb⟩,va⟩
  exact ⟨_,eq ▸ (P.property.1.sub inter_subset_left).card_vertices⟩

/-- For disjoint regions, prescribe a subdivision on each side, then complete
the remaining points freely. -/
theorem joint_local_bound (X Y Z : Finset V) (a b c : Nat) (yx : Y⊆X) (zx : Z⊆X)
    (d : Disjoint Y Z) (ya : Y.card=3*a) (zb : Z.card=3*b) (rem : X.card-(Y.card+Z.card)=3*c) :
    (localSeal X Y ∩ localSeal X Z).card≤ways a*ways b*ways c := by
  classical
  let E (P : Layout Y × Layout Z) := extensions X (P.1.val ∪ P.2.val)
  have cover : localSeal X Y ∩ localSeal X Z ⊆ univ.biUnion E := by
    intro D hd
    obtain ⟨P,p⟩ := local_seal_mem.mp (mem_inter.mp hd).1
    obtain ⟨Q,q⟩ := local_seal_mem.mp (mem_inter.mp hd).2
    exact mem_biUnion.mpr ⟨(P,Q),mem_univ _,mem_filter.mpr ⟨mem_univ _,union_subset p q⟩⟩
  have each (P : Layout Y × Layout Z) : (E P).card=ways c := by
    have ds : Disjoint (vertices P.1.val) (vertices P.2.val) := by rw [P.1.property.2,P.2.property.2]; exact d
    have eq : vertices (P.1.val ∪ P.2.val)=Y∪Z := by rw [vertices_union,P.1.property.2,P.2.property.2]
    exact extension_card X _ (P.1.property.1.combine P.2.property.1 ds) (eq.symm ▸ union_subset yx zx)
      c (by rw [eq,card_union_of_disjoint d,rem])
  apply (card_le_card cover).trans (card_biUnion_le.trans ?_)
  simp only [each,sum_const,card_univ,Fintype.card_prod,card_layout a Y ya,card_layout b Z zb,nsmul_eq_mul,Nat.cast_id,le_refl]

/-- The two-term inclusion-exclusion inequality in a form that counts ordered
pairs. It applies to families that have repeated or overlapping events. -/
theorem two_term {I Ω : Type} [DecidableEq I] [DecidableEq Ω] (S : Finset I) (F : I → Finset Ω) :
    2*(∑ i∈S,(F i).card) ≤ 2*(S.biUnion F).card+
      ∑ i∈S,∑ j∈S,if i=j then 0 else (F i∩F j).card := by
  classical
  let U := S.biUnion F
  let hit (x : Ω) := S.filter fun i => x∈F i
  have each (i) (hi : i∈S) : (F i).card=∑ x∈U,if x∈F i then 1 else 0 := by
    rw [sum_boole]
    congr 1
    ext x
    simp only [mem_filter]
    exact ⟨fun hx => ⟨mem_biUnion.mpr ⟨i,hi,hx⟩,hx⟩,And.right⟩
  have pair (i j) (hi : i∈S) :
      (if i=j then 0 else (F i∩F j).card)=∑ x∈U,if x∈F i ∧ x∈F j ∧ i≠j then 1 else 0 := by
    by_cases ij : i=j
    · simp [ij]
    · rw [if_neg ij,sum_boole]
      congr 1
      ext x
      simp only [mem_inter,mem_filter]
      exact ⟨fun h => ⟨mem_biUnion.mpr ⟨i,hi,h.1⟩,h.1,h.2,ij⟩,fun h => ⟨h.2.1,h.2.2.1⟩⟩
  have eq (x : Ω) : (∑ i∈S,∑ j∈S,if x∈F i ∧ x∈F j ∧ i≠j then 1 else 0) =
      (hit x).card*((hit x).card-1) := by
    have inner (i) : (∑ j∈S,if x∈F i ∧ x∈F j ∧ i≠j then 1 else 0) =
        if x∈F i then ((hit x).erase i).card else 0 := by
      by_cases xi : x∈F i
      · rw [if_pos xi,sum_boole,Nat.cast_id]
        congr 1
        ext j
        simp [hit,xi,ne_comm,and_comm,and_assoc,and_left_comm]
      · simp [xi]
    simp_rw [inner]
    rw [←sum_filter]
    change (∑ i∈hit x,((hit x).erase i).card)=_
    rw [sum_congr rfl (fun i hi => card_erase_of_mem hi),sum_const,nsmul_eq_mul,Nat.cast_id]
  have hs : ∑ i∈S,(F i).card=∑ x∈U,(hit x).card := by
    rw [sum_congr rfl each,sum_comm]
    simp only [sum_boole,hit,Nat.cast_id]
  have ps : (∑ i∈S,∑ j∈S,if i=j then 0 else (F i∩F j).card)=
      ∑ x∈U,(hit x).card*((hit x).card-1) := by
    calc
      _ = ∑ i∈S,∑ j∈S,∑ x∈U,if x∈F i ∧ x∈F j ∧ i≠j then 1 else 0 :=
        sum_congr rfl (fun i hi => sum_congr rfl (fun j _ => pair i j hi))
      _ = ∑ x∈U,∑ i∈S,∑ j∈S,if x∈F i ∧ x∈F j ∧ i≠j then 1 else 0 := by
        simp_rw [sum_comm (s:=S) (t:=U)]
      _ = _ := sum_congr rfl (fun x _ => eq x)
  rw [hs,ps,mul_sum]
  have per (x) : 2*(hit x).card ≤ 2+(hit x).card*((hit x).card-1) := by
    let k := (hit x).card
    change 2*k≤2+k*(k-1)
    by_cases small : k≤1
    · omega
    have h := Nat.mul_le_mul_right (k-1) (show 2≤k by omega)
    omega
  apply (sum_le_sum (s:=U) (fun x _ => per x)).trans
  simp [sum_add_distrib,nsmul_eq_mul,U,Nat.mul_comm]
end WildSieve
