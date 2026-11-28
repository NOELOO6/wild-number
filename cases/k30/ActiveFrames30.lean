import FramePlacement30

namespace WildSieve.Thirty.Graph
open Finset
local instance (priority := 2000) activeEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq
set_option maxRecDepth 10000
set_option maxHeartbeats 900000

noncomputable def frameEvent (L : Finset V) (P : Pattern) : Finset Deck := localSeal univ L∩event P

noncomputable def frames (F : Factor V C) (L : Finset V) (t : Fin 3) := (family F).filter
  (fun P => ((vertices P)∩L).card=6-3*t.val ∧ (frameEvent L P).Nonempty)

private theorem on_side (D : Deck) (L A : Finset V) (seen : D∈localSeal univ L) (a : A∈D.val) :
    A⊆L ∨ Disjoint A L := by
  by_cases split : Disjoint A L
  · exact Or.inr split
  · obtain ⟨v,hv⟩ := not_disjoint_iff_nonempty_inter.mp split
    exact Or.inl ((seal_whole (subset_univ _) D).mp seen A a v (mem_inter.mp hv).1 (mem_inter.mp hv).2)

private theorem locate (L A B : Finset V) (a : A.card=3) (b : B.card=3) (ab : Disjoint A B)
    (sa : A⊆L ∨ Disjoint A L) (sb : B⊆L ∨ Disjoint B L) (t : Fin 3)
    (size : ((A∪B)∩L).card=6-3*t.val) : Placement L A B t ∨ Placement L B A t := by
  rw [union_inter_distrib_right,card_union_of_disjoint
    (ab.mono (inter_subset_left : A∩L⊆A) (inter_subset_left : B∩L⊆B))] at size
  have bound := t.isLt
  rcases sa with ha|ha <;> rcases sb with hb|hb
  · rw [inter_eq_left.mpr ha,inter_eq_left.mpr hb,a,b] at size
    exact Or.inl ⟨ab,fun x h => ⟨fun _ => by omega,fun _ => ha h⟩,
      fun x h => ⟨fun _ => by omega,fun _ => hb h⟩⟩
  · rw [inter_eq_left.mpr ha,disjoint_iff_inter_eq_empty.mp hb,card_empty,a] at size
    exact Or.inl ⟨ab,fun x h => ⟨fun _ => by omega,fun _ => ha h⟩,
      fun x h => ⟨fun l => False.elim (disjoint_left.mp hb h l),fun k => by omega⟩⟩
  · rw [disjoint_iff_inter_eq_empty.mp ha,inter_eq_left.mpr hb,card_empty,b] at size
    exact Or.inr ⟨ab.symm,fun x h => ⟨fun _ => by omega,fun _ => hb h⟩,
      fun x h => ⟨fun l => False.elim (disjoint_left.mp ha h l),fun k => by omega⟩⟩
  · rw [disjoint_iff_inter_eq_empty.mp ha,disjoint_iff_inter_eq_empty.mp hb,card_empty] at size
    exact Or.inl ⟨ab,fun x h => ⟨fun l => False.elim (disjoint_left.mp ha h l),fun k => by omega⟩,
      fun x h => ⟨fun l => False.elim (disjoint_left.mp hb h l),fun k => by omega⟩⟩

structure FrameData (L : Finset V) (t : Fin 3) (P : Pattern) (z : V → Fin 4) : Prop where
  sizes : ∀ i,(zone z i).card=zoneSize t i
  left : selected z (leftMask t)=L
  mark : selected z hitMask=vertices P
  decks : Regions.decks z=frameEvent L P

private theorem build_frame (L A B : Finset V) (t : Fin 3) (l : L.card=12) (a : A.card=3) (b : B.card=3)
    (placement : Placement L A B t) (kind : ((A∪B)∩L).card=6-3*t.val) :
    FrameData L t {A,B} (splitRegion L A B) := by
  obtain ⟨left,mark⟩ := split_selected L A B t placement
  refine ⟨split_sizes L A B t placement l a b kind,left,?_,?_⟩
  · simpa [vertices] using mark
  · ext D
    rw [split_decks L A B t placement a b]
    simp [frameEvent,event,extensions,and_assoc,insert_subset_iff]

theorem exists_frame (F : Factor V C) (L : Finset V) (l : L.card=12) (t : Fin 3) (P : Pattern)
    (hp : P∈frames F L t) : ∃ z,FrameData L t P z := by
  obtain ⟨member,kind,D,hd⟩ := mem_filter.mp hp
  obtain ⟨A,B,ne,rfl⟩ := card_eq_two.mp (pattern_size member)
  have ok := (SixCounts.pattern_mem.mp member).1
  have a : A.card=3 := ok.size _ (by simp)
  have b : B.card=3 := ok.size _ (by simp)
  have ab : Disjoint A B := ok.separate _ (by simp) _ (by simp) ne
  have both := (mem_filter.mp (mem_inter.mp hd).2).2
  have hA := on_side D L A (mem_inter.mp hd).1 (both (by simp))
  have hB := on_side D L B (mem_inter.mp hd).1 (both (by simp))
  have ve : vertices ({A,B} : Pattern)=A∪B := by ext x; simp [vertices]
  rw [ve] at kind
  rcases locate L A B a b ab hA hB t kind with pl|pl
  · exact ⟨_,build_frame L A B t l a b pl kind⟩
  · rw [pair_comm A B]
    exact ⟨_,build_frame L B A t l b a pl (by simpa only [union_comm B A] using kind)⟩

/-- Select one orientation for each distinguished unordered pair. All
subdivisions in the corresponding event use that same pair of triples. -/
noncomputable def regionOf (F : Factor V C) (L : Finset V) (t : Fin 3) (P : Pattern) : V → Fin 4 := by
  classical
  exact if h : L.card=12 ∧ P∈frames F L t then (exists_frame F L h.1 t P h.2).choose else fun _ => 0

theorem region_spec (F : Factor V C) (L : Finset V) (l : L.card=12) (t : Fin 3) (P : Pattern)
    (hp : P∈frames F L t) : FrameData L t P (regionOf F L t P) := by
  classical
  simp only [regionOf,dif_pos (And.intro l hp)]
  exact (exists_frame F L l t P hp).choose_spec

end WildSieve.Thirty.Graph
