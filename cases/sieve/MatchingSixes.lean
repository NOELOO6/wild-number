import EvenTriples
import PairRegions
namespace WildSieve
open Finset
variable {A C : Type} [LinearOrder A] [Fintype A] [Fintype C]

/-- The six-point sets inside U consisting of three edges of some color. -/
noncomputable def marks (F : Factor A C) (U : Finset A) := sides F ∅ U 6

omit [Fintype A] in
theorem mark_mem {F : Factor A C} {U Q : Finset A} :
    Q∈marks F U ↔ Q⊆U ∧ Q.card=6 ∧ ∃ c,Closed (F.f c) Q := by
  constructor
  · intro h
    obtain ⟨c,h⟩ := side_mem.mp h
    obtain ⟨sub,sz,cl⟩ := candidate_mem.mp h
    exact ⟨sub,sz,c,by simpa using cl⟩
  · rintro ⟨sub,sz,c,cl⟩
    exact side_mem.mpr ⟨c,candidate_mem.mpr ⟨sub,sz,by simpa using cl⟩⟩

theorem marks_filter (F : Factor A C) (U : Finset A) :
    marks F U=(marks F univ).filter (fun Q => Q⊆U) := by
  classical
  ext Q
  simp only [mem_filter,mark_mem,subset_univ,true_and]
  tauto

omit [Fintype A] [Fintype C] in
theorem close_lowers (F : Factor A C) (c : C) {U I : Finset A} (sub : I⊆lowerEnds (F.f c) U) :
    let f := F.f c
    let Q := I∪I.image f
    Q⊆U ∧ Q.card=2*I.card ∧ Closed f Q ∧ lowerEnds f Q=I := by
  classical
  let f := F.f c
  have lt (x) (hx : x∈I) : x<f x := (mem_filter.mp (sub hx)).2.1
  have rev (x) (hx : x∈I.image f) : f x<x := by
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
    simpa [f,F.invol c y] using lt y hy
  have d : Disjoint I (I.image f) := disjoint_left.mpr (fun x hi hx => (lt x hi).asymm (rev x hx))
  have cl : Closed f (I∪I.image f) := by
    intro x hx
    rcases mem_union.mp hx with h|h
    · exact mem_union_right _ (mem_image.mpr ⟨x,h,rfl⟩)
    · obtain ⟨y,hy,rfl⟩ := mem_image.mp h
      exact mem_union_left _ (show f (f y)∈I from by simpa [f,F.invol c y] using hy)
  refine ⟨union_subset (sub.trans (filter_subset _ _)) ?_,?_,cl,?_⟩
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
    exact (mem_filter.mp (sub hy)).2.2
  · rw [card_union_of_disjoint d,card_image_of_injective _ (F.invol c).injective];omega
  · ext x
    constructor
    · intro h
      exact (mem_union.mp (mem_filter.mp h).1).resolve_right (fun im => ((mem_filter.mp h).2.1).asymm (rev x im))
    · intro h
      exact mem_filter.mpr ⟨mem_union_left _ h,lt x h,mem_union_right _ (mem_image.mpr ⟨x,h,rfl⟩)⟩

omit [Fintype A] [Fintype C] in
/-- Count colored marks with their color labels retained. -/
theorem candidate_pairs (F : Factor A C) (c : C) (U : Finset A) (k : Nat) :
    (candidates F c ∅ U (2*k)).card=(Inside F c U).choose k := by
  classical
  let f := F.f c
  let P := (lowerEnds f U).powersetCard k
  have eq : candidates F c ∅ U (2*k) = P.image (fun I => I∪I.image f) := by
    ext Q
    constructor
    · intro h
      obtain ⟨qu,sz,cl⟩ := candidate_mem.mp h
      simp only [empty_union] at cl
      have num := closed_size (F.invol c) (F.moving c) cl
      exact mem_image.mpr ⟨lowerEnds f Q,mem_powersetCard.mpr ⟨lower_mono _ qu,by
        change Q.card=2*(lowerEnds f Q).card at num;omega⟩,recover_ends (F.invol c) (F.moving c) cl⟩
    · intro h
      obtain ⟨I,hi,rfl⟩ := mem_image.mp h
      obtain ⟨sub,sz⟩ := mem_powersetCard.mp hi
      obtain ⟨a,b,cl,_⟩ := close_lowers F c sub
      exact candidate_mem.mpr ⟨a,b.trans (congrArg (2*·) sz),by simpa using cl⟩
  have inj : Set.InjOn (fun I : Finset A => I∪I.image f) P := by
    intro I hi J hj e
    have first := (close_lowers F c (mem_powersetCard.mp hi).1).2.2.2
    have last := (close_lowers F c (mem_powersetCard.mp hj).1).2.2.2
    exact first.symm.trans ((congrArg (lowerEnds f) e).trans last)
  rw [eq,card_image_of_injOn inj,card_powersetCard]
  rfl

/-- Throwing away labels inside a subset loses at most as many duplicates
as throwing away labels on the full vertex set. -/
theorem localized_defect (F : Factor A C) (U : Finset A) :
    (∑ c,(Inside F c U).choose 3)+(marks F univ).card ≤
      (∑ c,(Inside F c univ).choose 3)+(marks F U).card := by
  classical
  let fam (c : C) := candidates F c ∅ univ 6
  let out (c : C) := (fam c).filter (fun Q => ¬Q⊆U)
  have per (c) : (Inside F c U).choose 3+(out c).card=(Inside F c univ).choose 3 := by
    have cut : (fam c).filter (fun Q => Q⊆U)=candidates F c ∅ U 6 := by
      ext Q
      simp only [fam,mem_filter,candidate_mem,subset_univ,true_and];tauto
    have h := filter_card_add_filter_neg_card_eq_card (fun Q => Q⊆U) (s:=fam c)
    rw [cut,candidate_pairs F c U 3,candidate_pairs F c univ 3] at h
    exact h
  have eq : marks F univ \ marks F U = univ.biUnion out := by
    ext Q
    rw [marks_filter F U]
    simp only [mem_sdiff,mem_filter,mem_biUnion,mem_univ,true_and,out,fam]
    have spec : Q∈marks F univ ↔ ∃ c,Q∈candidates F c ∅ univ 6 := side_mem
    rw [spec]
    constructor
    · rintro ⟨⟨c,h⟩,no⟩
      exact ⟨c,h,fun sub => no ⟨⟨c,h⟩,sub⟩⟩
    · rintro ⟨c,h,outside⟩
      exact ⟨⟨c,h⟩,fun h => outside h.2⟩
  have sub : marks F U⊆marks F univ := by rw [marks_filter];exact filter_subset _ _
  have card := card_biUnion_le (s:=univ) (t:=out)
  rw [←eq,card_sdiff sub] at card
  have s := sum_congr (s₁:=univ) rfl (fun c _ => per c)
  rw [sum_add_distrib] at s
  have b := card_le_card sub
  omega
end WildSieve
