import SteinerCoordinates
import SteinerCheck
import CyclicCutSound

namespace Wild15.Steiner
open Finset WildDeletion WildExact EdgeWalk
open WildExact.Rotation.CutTest

open WildSteiner

private theorem facts : layouts.all (fun bs => points.all (fun x => bs.flatten.contains x) &&
    (drawing bs).length==10 && (drawing bs).all fun e => e.1 != e.2)=true := by native_decide

private theorem opposite_line (S : System V) (T : Block) (h : Genuine S T) (c x y : V)
    (found : opposite T c=some (x,y)) : x≠y ∧ S.third x y=c := by
  obtain ⟨ab,third⟩ := h
  have ac : T.a≠T.c := by rw [←third];exact (S.left_ne ab).symm
  have bc : T.b≠T.c := by rw [←third];exact (S.right_ne ab).symm
  unfold opposite at found
  split at found
  · rename_i eq
    cases found
    exact ⟨bc,eq ▸ (third ▸ S.recover T.a T.b)⟩
  · split at found
    · rename_i eq
      cases found
      exact ⟨ac,eq ▸ (third ▸ S.again T.a T.b)⟩
    · split at found
      · rename_i eq
        cases found
        exact ⟨ab,third.trans eq.symm⟩
      · contradiction

/-- Recolor any of the edges in the two named color classes, retaining
a proper coloring and the other color classes. -/
structure Redraw (g : Coloring 15 15) (a b : V) (h : Coloring 15 15) : Prop where
  flexible : ∀ x y,x≠y → g.paint x y=a ∨ g.paint x y=b → h.paint x y=a ∨ h.paint x y=b
  fixed : ∀ x y,x≠y → g.paint x y≠a → g.paint x y≠b → h.paint x y=g.paint x y

theorem Redraw.refl (g : Coloring 15 15) (a b : V) : Redraw g a b g :=
  ⟨fun _ _ _ col => col,fun _ _ _ _ _ => rfl⟩

private theorem oriented_line (S : System V) (ts : List Block) (real : ∀ T∈ts,Genuine S T)
    (i x y : V) (e : (x,y)∈oriented ts i) : x≠y ∧ S.third x y=i := by
  have edge (u v : V) (h : (u,v)∈edgesOf ts i) : u≠v ∧ S.third u v=i := by
    obtain ⟨T,mem,opp⟩ := List.mem_filterMap.mp h
    exact opposite_line S T (real T mem) i u v opp
  rcases List.mem_append.mp e with h|h
  · exact edge _ _ h
  · obtain ⟨⟨v,u⟩,mem,eq⟩ := List.mem_map.mp h
    cases eq
    obtain ⟨ne,col⟩ := edge _ _ mem
    exact ⟨ne.symm,(S.swap _ _).trans col⟩

/-- For any two named colors of a Steiner coloring, one set of ten
wild edges works simultaneously for all their proper redraws. -/
theorem common_two (g : Coloring 15 15) (data : SteinerColoring g) (a b : V) (ab : a≠b) :
    ∃ W : Lines 15,Legal W ∧ W.card=10 ∧ ∀ h,Redraw g a b h → Works h W := by
  classical
  obtain ⟨S,paint⟩ := data
  have epi := Finite.injective_iff_surjective.mp (missing_injective (by decide : 15%2=1) g)
  obtain ⟨u,hu⟩ := epi a
  obtain ⟨v,hv⟩ := epi b
  have uv : u≠v := fun e => ab (hu.symm.trans (e ▸ hv))
  obtain ⟨w,cs,hcs,w0,w1,start⟩ := coordinates_at S u v uv
  obtain ⟨ts,ok,real⟩ := extract (S.reindex w) (works (tables cs)) 22 _ start
    (List.all_eq_true.mp exhaustive cs hcs)
  obtain ⟨t,ht,ok⟩ := List.any_eq_true.mp ok
  obtain ⟨bs,hb,rfl⟩ := List.mem_map.mp ht
  obtain ⟨inList,centers⟩ := List.mem_filter.mp hb
  obtain ⟨pre,legal⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp facts _ inList)
  obtain ⟨cover,sz⟩ := Bool.and_eq_true_iff.mp pre
  let es := drawing bs
  let line (e : Pair) : Pair := (min (w e.1) (w e.2),max (w e.1) (w e.2))
  let W := es.toFinset.image line
  have touch (x y : V) (e : (x,y)∈es) : Touch W (w x) (w y) := by
    have mem : line (x,y)∈W := mem_image_of_mem line (List.mem_toFinset.mpr e)
    rcases le_total (w x) (w y) with l|l
    · exact Or.inl (by simpa [line,l] using mem)
    · exact Or.inr (by simpa [line,l] using mem)
  have clean : Legal W := by
    intro e he
    obtain ⟨p,hp,rfl⟩ := mem_image.mp he
    have ne := w.injective.ne (bne_iff_ne.mp (List.all_eq_true.mp legal _ (List.mem_toFinset.mp hp)))
    rcases lt_or_gt_of_ne ne with h|h <;> simp [line,h,h.le]
  have cov (x : V) : x∈bs.flatten := List.contains_iff_mem.mp (List.all_eq_true.mp cover x (List.mem_finRange _))
  have orig (ss : List Block) (genuine : ∀ T∈ss,Genuine (S.reindex w) T)
      (i x y : V) (e : (x,y)∈oriented ss i) : w x≠w y ∧ g.paint (w x) (w y)=missingColor g (w i) := by
    obtain ⟨ne,third⟩ := oriented_line _ ss genuine i x y e
    exact ⟨w.injective.ne ne,(paint _ _ (w.injective.ne ne)).trans (congrArg _ (w.symm_apply_eq.mp third))⟩
  have win (h : Coloring 15 15) (recolor : Redraw g a b h) : Works h W := by
    intro c
    let R (x y : V) := Joined h W c (w x) (w y)
    suffices paths : Connected R by
      intro x y
      simpa only [Equiv.apply_symm_apply] using
        (Walk.mapInto w (fun _ _ step => Walk.step (Walk.stay _) step) (paths (w.symm x) (w.symm y)) :
          Walk (Joined h W c) (w (w.symm x)) (w (w.symm y)))
    by_cases flexible : c=a ∨ c=b
    · apply connected_of_crossings bs cov R (joined_symm h)
      · intro B hB x y hx hy
        have path := block_walk bs B hB [] x y hx hy
        apply Walk.mapInto id _ path
        intro j k ordinary
        rcases ordinary with e|e
        · exact .step (.stay _) (Or.inl (touch _ _ (by simpa using e)))
        · exact .step (.stay _) (joined_symm h (Or.inl (touch _ _ (by simpa using e))))
      · intro side inside
        obtain ⟨⟨x,y⟩,line0,hits⟩ := List.any_eq_true.mp (List.all_eq_true.mp centers side inside)
        obtain ⟨⟨x',z⟩,line1,bits⟩ := List.any_eq_true.mp hits
        simp only [Bool.and_eq_true,beq_iff_eq,bne_iff_ne] at bits
        obtain ⟨⟨⟨rfl,yz⟩,cy⟩,cz⟩ := bits
        obtain ⟨xy,color0⟩ := orig _ start 0 x y line0
        obtain ⟨xz,color1⟩ := orig _ start 1 x z line1
        rw [w0,hu] at color0
        rw [w1,hv] at color1
        have h0 := recolor.flexible _ _ xy (Or.inl color0)
        have h1 := recolor.flexible _ _ xz (Or.inr color1)
        have distinct : h.paint (w x) (w y)≠h.paint (w x) (w z) :=
          fun eq => yz (w.injective (h.proper _ _ _ xy xz eq))
        have hit : h.paint (w x) (w y)=c ∨ h.paint (w x) (w z)=c := by
          rcases flexible with rfl|rfl <;> rcases h0 with h0|h0 <;> rcases h1 with h1|h1 <;> simp_all
        have diff (s t : V) (neq : side.contains s ≠ side.contains t) : ¬(s∈side ↔ t∈side) :=
          fun eq => neq (Bool.eq_iff_iff.mpr (by simpa using eq))
        rcases hit with yes|yes
        · exact ⟨x,y,Or.inr ⟨xy,yes⟩,diff _ _ cy⟩
        · exact ⟨x,z,Or.inr ⟨xz,yes⟩,diff _ _ cz⟩
    · obtain ⟨z,hz⟩ := epi c
      let i := w.symm z
      have check := beq_iff_eq.mp (List.all_eq_true.mp ok (edgesOf ts i) (List.mem_map.mpr ⟨i,List.mem_finRange _,rfl⟩))
      have base : Connected (Adj (es++edgesOf ts i)) := by
        simpa [Rotation.shift,es] using connected_row bs cov (edgesOf ts i) 0 check
      have forward (x y : V) (he : (x,y)∈es++edgesOf ts i) : R x y := by
        rcases List.mem_append.mp he with wild|col
        · exact Or.inl (touch _ _ wild)
        obtain ⟨ne,painted⟩ := orig ts real i x y (List.mem_append_left _ col)
        have eq : g.paint (w x) (w y)=c := by simpa [i] using painted.trans (by simpa [i] using hz)
        exact Or.inr ⟨ne,(recolor.fixed _ _ ne (fun p => flexible (Or.inl (eq.symm.trans p)))
          (fun p => flexible (Or.inr (eq.symm.trans p)))).trans eq⟩
      intro x y
      apply Walk.mapInto id _ (base x y)
      intro j k edge
      exact .step (.stay _) (edge.elim (forward _ _) (fun rev => joined_symm h (forward _ _ rev)))
  have lo : 10≤W.card := odd_lower (by decide : 3≤15) g clean (win g (Redraw.refl g a b))
  exact ⟨W,clean,le_antisymm (card_image_le.trans (es.toFinset_card_le.trans (beq_iff_eq.mp sz).le)) lo,win⟩

theorem exact_redraw (g h : Coloring 15 15) (data : SteinerColoring g) (a b : V) (ne : a≠b)
    (recolor : Redraw g a b h) : Exact h 10 := by
  obtain ⟨w,legal,sz,win⟩ := common_two g data a b ne
  exact ⟨⟨w,legal,sz,win h recolor⟩,fun _ => odd_lower (by decide) h⟩

theorem exact_K15 (g : Coloring 15 15) (data : SteinerColoring g) : Exact g 10 :=
  exact_redraw g g data 0 1 (by decide) (Redraw.refl g 0 1)

theorem exact_deletion_K16 (g : Coloring 16 15) (data : SteinerColoring (restrict g)) : Exact g 10 := by
  obtain ⟨⟨w,legal,sz,win⟩,_⟩ := exact_K15 (restrict g) data
  exact exact_of_upper (upper_from_deletion g ⟨w,legal,sz.le,win⟩) (fun _ => even_lower (by decide) g)

#print axioms common_two
#print axioms exact_K15
#print axioms exact_deletion_K16
end Wild15.Steiner
