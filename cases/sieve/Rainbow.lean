import Factors
namespace WildSieve
open Finset
variable {A C : Type} [LinearOrder A] [Fintype A] [Fintype C]

theorem rainbow_insert (F : Factor A C) (B : Finset A) (r : Rainbow F B)
    (room : B.card+B.card.choose 2*B.card < Fintype.card A) :
    ∃ x ∉ B, Rainbow F (insert x B) := by
  classical
  let used := univ.filter (fun c => 0 < Inside F c B)
  let bad := B ∪ used.biUnion (fun c => B.image (F.f c))
  have count : bad.card ≤ B.card+B.card.choose 2*B.card := by
    apply (Finset.card_union_le _ _).trans
    apply Nat.add_le_add_left
    apply card_biUnion_le.trans
    rw [← color_count F r]
    calc
      _ ≤ ∑ _ ∈ used,B.card := sum_le_sum (fun c _ => card_image_le)
      _ = _ := by simp [used]
  have lt : bad.card < (univ : Finset A).card := by simpa using count.trans_lt room
  obtain ⟨x,_,nx⟩ := exists_mem_not_mem_of_card_lt_card lt
  have nxB : x ∉ B := fun hx => nx (mem_union_left _ hx)
  refine ⟨x,nxB,fun c => ?_⟩
  by_cases seen : 0 < Inside F c B
  · apply (card_le_card (t := lowerEnds (F.f c) B) _).trans (r c)
    intro a ha
    obtain ⟨ax,lt,fx⟩ := mem_filter.mp ha
    have avoid (b : A) (bb : b∈B) : F.f c b≠x := fun eq =>
      nx (mem_union_right _ (mem_biUnion.mpr ⟨c,mem_filter.mpr ⟨mem_univ _,seen⟩,mem_image.mpr ⟨b,bb,eq⟩⟩))
    rcases mem_insert.mp ax with rfl|aB
    · have fxB := (mem_insert.mp fx).resolve_left (F.moving c a).symm
      exact False.elim (avoid _ fxB (F.invol c a))
    · exact mem_filter.mpr ⟨aB,lt,(mem_insert.mp fx).resolve_left (avoid a aB)⟩
  · have sub : lowerEnds (F.f c) (insert x B) ⊆ insert (min x (F.f c x)) (lowerEnds (F.f c) B) := by
      intro a ha
      obtain ⟨ax,lt,fx⟩ := mem_filter.mp ha
      rcases mem_insert.mp ax with rfl|aa
      · exact mem_insert.mpr (Or.inl (min_eq_left lt.le).symm)
      · rcases mem_insert.mp fx with eq|fb
        · have aeq : F.f c x=a := eq ▸ F.invol c a
          apply mem_insert.mpr (Or.inl ?_)
          rw [aeq]
          exact (min_eq_right (eq ▸ lt.le)).symm
        · exact mem_insert_of_mem (mem_filter.mpr ⟨aa,lt,fb⟩)
    have cap := (card_le_card sub).trans (card_insert_le _ _)
    change ¬0 < (lowerEnds (F.f c) B).card at seen
    change (lowerEnds (F.f c) (insert x B)).card ≤ 1
    omega

theorem rainbow_at_root [Nonempty A] (F : Factor A C) (root : A) (k : Nat)
    (room : ∀ b, 1 ≤ b → b ≤ k → b + b.choose 2*b < Fintype.card A) :
    ∃ B : Finset A, root ∈ B ∧ B.card=k+1 ∧ Rainbow F B := by
  classical
  induction k with
  | zero =>
    refine ⟨{root},by simp,by simp,fun c => ?_⟩
    exact (card_le_card (filter_subset _ _)).trans (card_singleton _).le
  | succ k ih =>
    obtain ⟨B,rootB,bsize,r⟩ := ih (fun b lo hi => room b lo (by omega))
    obtain ⟨x,nx,new⟩ := rainbow_insert F B r (room B.card (by omega) (by omega))
    exact ⟨insert x B,mem_insert_of_mem rootB,by simp [nx,bsize],new⟩
end WildSieve
