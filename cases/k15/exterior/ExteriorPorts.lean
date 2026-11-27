import ExteriorTotals
import FrozenStats
namespace WildExterior
open Finset WildSieve
abbrev V := Fin 16

def outside (i : Port ↪ V) := univ.map i
theorem outside_mem {i : Port ↪ V} {v : V} : v∈outside i ↔ ∃ x,i x=v := by simp [outside]
theorem port_inside (i : Port ↪ V) (x : Port) : i x∈outside i := outside_mem.mpr ⟨x,rfl⟩
theorem nine (i : Port ↪ V) : (outside i).card=9 := by simp [outside]
theorem seven (i : Port ↪ V) : (outside i)ᶜ.card=7 := by rw [card_compl,Fintype.card_fin,nine]

noncomputable def ordinary (F : Factor V Color) (i : Port ↪ V) (c : Color) : Pairs := by
  classical exact pairs9.filter (fun q => Closed (F.f c) (q.map i))
noncomputable def tap (F : Factor V Color) (i : Port ↪ V) (r : V) (c : Color) : Option Port := by
  classical
  exact if h : ∃ x,i x=F.f c r then some h.choose else none

theorem tap_spec (F : Factor V Color) (i : Port ↪ V) (r : V) (c : Color) (x : Port) :
    x∈star (tap F i r c) ↔ i x=F.f c r := by
  classical
  by_cases found : ∃ v,i v=F.f c r
  · simp only [tap,dif_pos found,star,Option.toList_some,List.toFinset_cons,List.toFinset_nil,
      insert_empty_eq,mem_singleton]
    exact ⟨fun eq => eq.symm ▸ found.choose_spec,fun eq => i.injective (eq.trans found.choose_spec.symm)⟩
  · simp [tap,found,star,show i x≠F.f c r from fun h => found ⟨x,h⟩]

theorem ordinary_mem {F : Factor V Color} {i : Port ↪ V} {c : Color} {q : Finset Port} :
    q∈ordinary F i c ↔ q.card=2 ∧ Closed (F.f c) (q.map i) := by
  classical
  simp [ordinary,pairs9]

private theorem edge_partner (F : Factor V Color) (i : Port ↪ V) (c : Color)
    {q : Finset Port} (hq : q∈ordinary F i c) {x} (hx : x∈q) :
    ∃ y,x≠y ∧ i y=F.f c (i x) ∧ q={x,y} := by
  obtain ⟨a,b,ab,eq⟩ := card_eq_two.mp (ordinary_mem.mp hq).1
  obtain ⟨y,xy,pair⟩ : ∃ y,x≠y ∧ q={x,y} := by
    rw [eq,mem_insert,mem_singleton] at hx
    rcases hx with rfl|rfl
    · exact ⟨b,ab,eq⟩
    · exact ⟨a,ab.symm,eq.trans (Finset.pair_comm a x)⟩
  have cl := (ordinary_mem.mp hq).2 (i x) (mem_map.mpr ⟨x,hx,rfl⟩)
  obtain ⟨z,zq,ze⟩ := mem_map.mp cl
  rw [pair,mem_insert,mem_singleton] at zq
  have zy := zq.resolve_left (fun e => F.moving c (i x) (e ▸ ze))
  exact ⟨y,xy,zy ▸ ze,pair⟩

theorem inside_partners (F : Factor V Color) (i : Port ↪ V) (c : Color) (x : Port) :
    x∈used (ordinary F i c) ↔ F.f c (i x)∈outside i := by
  constructor
  · intro h
    obtain ⟨q,hq,xt⟩ := mem_biUnion.mp h
    obtain ⟨y,_,eq,_⟩ := edge_partner F i c hq xt
    exact outside_mem.mpr ⟨y,eq⟩
  · intro h
    obtain ⟨y,eq⟩ := outside_mem.mp h
    have xy : x≠y := fun e => F.moving c (i x) (e.symm ▸ eq)
    have q : {x,y}∈ordinary F i c := ordinary_mem.mpr ⟨by simp [xy],by
      intro v hv
      obtain ⟨a,ha,rfl⟩ := mem_map.mp hv
      rcases mem_insert.mp ha with e|e
      · subst a
        exact mem_map.mpr ⟨y,mem_insert_of_mem (mem_singleton_self _),eq⟩
      · have ay := mem_singleton.mp e
        subst a
        exact mem_map.mpr ⟨x,mem_insert_self _ _,((congrArg (F.f c) eq).trans (F.invol c (i x))).symm⟩⟩
    exact mem_biUnion.mpr ⟨{x,y},q,mem_insert_self _ _⟩

private theorem paired_mem {A : Type} [LinearOrder A] {f : A → A} {S : Finset A} {x : A} :
    x∈paired f S ↔ x∈S ∧ f x∈S := mem_filter

theorem ordinary_counts (F : Factor V Color) (i : Port ↪ V) (c : Color) :
    (used (ordinary F i c)).card=2*(ordinary F i c).card ∧
      (ordinary F i c).card=Inside F c (outside i) := by
  let p := ordinary F i c
  have dis : (p : Set (Finset Port)).PairwiseDisjoint id := by
    intro a ha b hb ne
    apply disjoint_left.mpr
    intro x xa xb
    obtain ⟨v,_,vEq,va⟩ := edge_partner F i c ha xa
    obtain ⟨z,_,zEq,zb⟩ := edge_partner F i c hb xb
    exact ne (va.trans ((i.injective (vEq.trans zEq.symm)) ▸ zb.symm))
  have sz : (used p).card=2*p.card := by
    rw [used,card_biUnion dis]
    change (∑ e∈p,e.card)=_
    rw [sum_congr rfl (fun e (h : e∈p) => (ordinary_mem.mp h).1),sum_const]
    simp [Nat.mul_comm]
  have eq : (used p).map i=paired (F.f c) (outside i) := by
    ext v
    constructor
    · intro h
      obtain ⟨x,hx,rfl⟩ := mem_map.mp h
      exact paired_mem.mpr ⟨port_inside i x,(inside_partners F i c x).mp hx⟩
    · intro h
      obtain ⟨a,b⟩ := paired_mem.mp h
      obtain ⟨x,rfl⟩ := outside_mem.mp a
      exact mem_map.mpr ⟨x,(inside_partners F i c x).mpr b,rfl⟩
  have n := congrArg Finset.card eq
  rw [card_map,paired_size (F.invol c) (F.moving c),sz] at n
  exact ⟨sz,Nat.eq_of_mul_eq_mul_left (by decide : 0<2) n⟩

theorem partners_in (F : Factor V Color) (v : V) (S : Finset V) :
    (univ.filter (fun c => F.f c v∈S)).card=(S.erase v).card := by
  classical
  let H := univ.filter (fun c => F.f c v∈S)
  have eq : H.image (fun c => F.f c v)=S.erase v := by
    ext x
    constructor
    · intro h
      obtain ⟨c,hc,rfl⟩ := mem_image.mp h
      exact mem_erase.mpr ⟨(F.moving c v).symm,(mem_filter.mp hc).2⟩
    · intro h
      obtain ⟨ne,ins⟩ := mem_erase.mp h
      obtain ⟨c,cv⟩ := F.edge v x ne.symm
      exact mem_image.mpr ⟨c,mem_filter.mpr ⟨mem_univ _,cv.symm ▸ ins⟩,cv⟩
  simpa only [card_image_of_injective _ (F.unique v)] using congrArg Finset.card eq

theorem tap_set (F : Factor V Color) (i : Port ↪ V) (r : V) (out : r∉outside i) (W : Finset Port) :
    (∑ c,((star (tap F i r c))∩W).card)=W.card := by
  classical
  have each (c) : ((star (tap F i r c))∩W).card=if F.f c r∈W.map i then 1 else 0 := by
    by_cases mem : F.f c r∈W.map i
    · obtain ⟨x,xw,xe⟩ := mem_map.mp mem
      have eq : star (tap F i r c)∩W={x} := by
        ext y
        rw [mem_inter,mem_singleton,tap_spec]
        exact ⟨fun h => i.injective (h.1.trans xe.symm),fun e => e.symm ▸ ⟨xe,xw⟩⟩
      rw [eq,if_pos mem,card_singleton]
    · have eq : star (tap F i r c)∩W=∅ := eq_empty_iff_forall_not_mem.mpr (fun x h =>
        mem (mem_map.mpr ⟨x,(mem_inter.mp h).2,(tap_spec _ _ _ _ _).mp (mem_inter.mp h).1⟩))
      rw [eq,if_neg mem,card_empty]
  have no : r∉W.map i := by
    intro h
    obtain ⟨x,_,e⟩ := mem_map.mp h
    exact out (outside_mem.mpr ⟨x,e⟩)
  rw [sum_congr rfl (fun c _ => each c),sum_boole,partners_in,erase_eq_of_not_mem no,card_map]
  rfl
end WildExterior
