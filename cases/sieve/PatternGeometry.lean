import PatternPairs
import LongCredit

namespace WildSieve.SixCounts
open Finset
variable {n k : Nat}
local notation "V" => Fin n
local notation "C" => Fin k
local notation "Pattern" => Blocks V
local instance (priority := 2000) geometryEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq

theorem two_from {P : Pattern} (two : P.card=2) {A : Finset V} (h : A∈P) :
    ∃ B, A≠B ∧ P={A,B} := by
  have s : (P.erase A).card=1 := by rw [card_erase_of_mem h,two]
  obtain ⟨B,eq⟩ := card_eq_one.mp s
  refine ⟨B,?_,?_⟩
  · rintro rfl
    exact Finset.not_mem_erase A P (eq ▸ mem_singleton_self A)
  · rw [←insert_erase h,eq]

theorem wedge_view {F : Factor V C} {P Q : Pattern} (hp : P∈family F) (hq : Q∈family F)
    (h : Wedge P Q) : ∃ A B D : Finset V, P={A,B} ∧ Q={A,D} ∧ A≠B ∧ A≠D ∧ B≠D := by
  obtain ⟨A,mem⟩ := not_disjoint_iff_nonempty_inter.mp h.2.2
  obtain ⟨B,ab,p⟩ := two_from (pattern_size hp) (mem_inter.mp mem).1
  obtain ⟨D,ad,q⟩ := two_from (pattern_size hq) (mem_inter.mp mem).2
  exact ⟨A,B,D,p,q,ab,ad,fun e => h.1 (by rw [p,q,e])⟩

theorem wedge_size {F : Factor V C} {P Q : Pattern} (hp : P∈family F) (hq : Q∈family F)
    (h : Wedge P Q) : (P∪Q).card=3 := by
  obtain ⟨A,B,D,rfl,rfl,ab,ad,bd⟩ := wedge_view hp hq h
  have eq : ({A,B} : Pattern)∪{A,D}={A,B,D} := by ext X; simp only [mem_union,mem_insert,mem_singleton]; tauto
  rw [eq]; simp [ab,ad,bd]

theorem through_le (F : Factor V C) (A : Finset V) (size : A.card=3) :
    ((family F).filter (fun P => A∈P)).card≤k+3*(n/2-3) := by
  classical
  have sub : (family F).filter (fun P => A∈P)⊆(neighbors F A).image (fun B => ({A,B} : Pattern)) := by
    intro P h
    obtain ⟨hp,mem⟩ := mem_filter.mp h
    obtain ⟨B,ab,rfl⟩ := two_from (pattern_size hp) mem
    exact mem_image.mpr ⟨B,other_neighbor ab hp,rfl⟩
  exact (card_le_card sub).trans (card_image_le.trans (degree_le F A size))

noncomputable abbrev event (P : Pattern) := extensions (univ : Finset V) P

theorem event_union (P Q : Pattern) : event P∩event Q=event (P∪Q) := by
  classical ext D; simp [extensions,union_subset_iff]

theorem event_mass (t : Nat) (order : n=3*t) {P : Pattern} (ok : Triples P) :
    (event P).card=ways (t-P.card) := by
  apply extension_card _ _ ok (subset_univ _)
  have sz := ok.card_vertices
  have cap := (vertices P).card_le_univ
  simp only [card_univ,Fintype.card_fin] at cap ⊢
  omega

theorem event_empty {P : Pattern} (no : ¬Triples P) : (event P).card=0 := by
  classical
  apply card_eq_zero.mpr (eq_empty_iff_forall_not_mem.mpr ?_)
  intro D h
  exact no (D.property.1.sub (mem_filter.mp h).2)

theorem event_pattern_union (F : Factor V C) :
    (family F).biUnion event=(noSix F univ)ᶜ := by
  classical
  ext D
  constructor
  · intro h
    obtain ⟨M,hm,md⟩ := mem_biUnion.mp h
    obtain ⟨ok,mark⟩ := pattern_mem.mp hm
    apply mem_compl.mpr
    intro no
    exact noSix_mem.mp no _ mark (local_seal_mem.mpr ⟨⟨M,ok,rfl⟩,(mem_filter.mp md).2⟩)
  · intro h
    have no : ¬(∀ Q∈marks F univ,D∉localSeal univ Q) := fun w => mem_compl.mp h (noSix_mem.mpr w)
    push_neg at no
    obtain ⟨Q,hq,hit⟩ := no
    obtain ⟨M,sub⟩ := local_seal_mem.mp hit
    exact mem_biUnion.mpr ⟨M.val,pattern_mem.mpr ⟨M.property.1,M.property.2.symm ▸ hq⟩,
      mem_filter.mpr ⟨mem_univ _,sub⟩⟩

end WildSieve.SixCounts
