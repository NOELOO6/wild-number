import CoreSplit
namespace WildCuts.OneExtra
open Finset WildExact WildSieve WildDeletion EdgeWalk

private theorem exterior_budget {n t : Nat} (b : Blocks (Fin n) (Fin t))
    (p : Equiv.Perm (Fin n)) (U : Finset (Fin t)) :
    (outsideStars b p U).card+((core b p U).card-U.card)≤n-t := by
  classical
  let f (j) := width b j
  have pos (j) : 0<f j := card_pos.mpr ⟨b.rep j,mem_filter.mpr ⟨mem_univ _,b.section_ j⟩⟩
  have card (S : Finset (Fin t)) : (core b p S).card=∑ j∈S,f j := by rw [core,card_map,side_count]
  have decomp (S : Finset (Fin t)) : (∑ j∈S,(f j-1))+S.card=∑ j∈S,f j := by
    calc
      _ = ∑ j∈S,((f j-1)+1) := by simp [sum_add_distrib]
      _ = _ := sum_congr rfl (fun j _ => by have := pos j;omega)
  have full : (∑ j,f j)=n := by
    rw [←side_count b univ]
    simp [side]
  have lim : (outsideStars b p U).card≤∑ j∈Uᶜ,(f j-1) := by
    apply card_biUnion_le.trans (sum_le_sum ?_)
    intro j _
    simpa only [card,sum_singleton] using spokes_bound (core b p {j})
  have left := decomp U
  have right := decomp Uᶜ
  have sum := sum_compl_add_sum U f
  have count := @card_compl _ _ _ U
  have cap : U.card≤t := U.card_le_univ.trans_eq (Fintype.card_fin t)
  rw [full] at sum
  simp only [Fintype.card_fin] at count
  rw [card]
  omega

/-- Only the two groups containing the two ends of the repair edge need to
be reopened. If both ends are in one group, any second group may be chosen. -/
theorem two_group_reduction (i : Nat) (small : i<34) (g : Coloring (order i) (order i)) :
    ∃ (p : Equiv.Perm (Fin (order i))) (U : Finset (Fin (regular i+1))),
      let R := core (template i) p U
      let w := outsideStars (template i) p U
      U.card=2 ∧ R.card=6+(if Fin.last (regular i)∈U then order i%3 else 0) ∧
      Legal w ∧ w.card+(R.card-2)≤(2*order i+2)/3 ∧ MeetsCore g w R := by
  classical
  obtain ⟨p,a,z,_,connected⟩ := repaired_layout i small g
  let b := template i
  let ga := b.tag (p.symm a)
  let gz := b.tag (p.symm z)
  let r := Fin.last (regular i)
  have two : ({ga,gz} : Finset _).card≤2 := by simpa using card_insert_le ga ({gz} : Finset _)
  obtain ⟨U,sub,sz⟩ := exists_superset_card_eq two
    (show 2≤Fintype.card (Fin (regular i+1)) by simp [regular,order];omega)
  have ma : a∈core b p U := in_core.mpr (sub (by change ga∈({ga,gz} : Finset _);simp))
  have mz : z∈core b p U := in_core.mpr (sub (by change gz∈({ga,gz} : Finset _);simp))
  have sizes (j) : width b j=if j=r then 3+order i%3 else 3 := template_widths ⟨i,small⟩ j
  refine ⟨p,U,sz,?_,?_,?_,exterior_reaches g b p U (fun c => strip b p U ma mz _ (connected c))⟩
  · rw [core,card_map,side_count]
    change (∑ j∈U,width b j)=6+(if r∈U then order i%3 else 0)
    by_cases hr : r∈U
    · rw [if_pos hr,←sum_erase_add U _ hr]
      have ex : (∑ j∈U.erase r,width b j)=(U.erase r).card*3 :=
        sum_const_nat fun j hj => (sizes j).trans (if_neg (mem_erase.mp hj).1)
      rw [ex,card_erase_of_mem hr,sz,sizes,if_pos rfl]
      omega
    · have ex : (∑ j∈U,width b j)=U.card*3 :=
        sum_const_nat fun j hj => (sizes j).trans (if_neg (show j≠r from fun jr => hr (jr ▸ hj)))
      rw [if_neg hr,ex,sz]
  · intro e he
    obtain ⟨_,_,hit⟩ := mem_biUnion.mp he
    exact spokes_legal _ e hit
  · have h := exterior_budget b p U
    rw [sz] at h
    exact h.trans_eq (by dsimp [regular,order];omega)

/-- With the exterior fixed, a successful two-way split needs one crossing
path in each color. Drawing two stars then costs at most |R|-2 edges. -/
theorem upper_if_two {n k limit : Nat} (pos : 0<k) (g : Coloring n k) (w : Lines n) (R A B : Finset (Fin n))
    (legal : Legal w) (reach : MeetsCore g w R) (cover : A∪B=R) (apart : Disjoint A B)
    (paths : ∀ c,∃ x∈A,∃ y∈B,Walk (Joined g w c) x y)
    (budget : w.card+(R.card-2)≤limit) : Upper g limit := by
  classical
  let all := w∪spokes A∪spokes B
  have subA : spokes A⊆all := fun _ h => mem_union_left _ (mem_union_right _ h)
  have subB : spokes B⊆all := fun _ h => mem_union_right _ h
  refine ⟨all,?_,?_,?_⟩
  · intro e he
    rcases mem_union.mp he with wa|eb
    · exact (mem_union.mp wa).elim (legal e) (spokes_legal A e)
    · exact spokes_legal B e eb
  · obtain ⟨x,hx,y,hy,_⟩ := paths ⟨0,by omega⟩
    have pa := card_pos.mpr (show A.Nonempty from ⟨x,hx⟩)
    have pb := card_pos.mpr (show B.Nonempty from ⟨y,hy⟩)
    have cs : R.card=A.card+B.card := cover ▸ card_union_of_disjoint apart
    have a := spokes_bound A
    have b := spokes_bound B
    have ab := card_union_le w (spokes A)
    have fin := card_union_le (w∪spokes A) (spokes B)
    change (w∪spokes A∪spokes B).card≤_
    omega
  intro c
  obtain ⟨u,hu,v,hv,path⟩ := paths c
  let E := Joined g all c
  have lift {x y} : Joined g w c x y → E x y := by
    rintro ((h|h)|h)
    · exact Or.inl (Or.inl (mem_union_left _ (mem_union_left _ h)))
    · exact Or.inl (Or.inr (mem_union_left _ (mem_union_left _ h)))
    · exact Or.inr h
  have across : Walk E u v := Walk.mapInto id (fun _ _ h => .step (.stay _) (lift h)) path
  have star {D x y} (inc : spokes D⊆all) (hx : x∈D) (hy : y∈D) : Walk E x y :=
    Walk.mapInto (E:=Touch all) (F:=E) id (fun _ _ h => .step (.stay _) (Or.inl h)) (in_star inc hx hy)
  have from_u (x) (hx : x∈R) : Walk E u x := by
    rcases mem_union.mp (cover.symm ▸ hx) with ax|bx
    · exact star subA hu ax
    · exact across.join (star subB hv bx)
  apply (complete_on_core (reach c) lift (joined_symm g)).mpr
  exact fun x hx y hy => (backwards (joined_symm g) (from_u x hx)).join (from_u y hy)

theorem exact_if_two {n : Nat} (hn : 3≤n) (g : Coloring n n) (w : Lines n) (R A B : Finset (Fin n))
    (legal : Legal w) (reach : MeetsCore g w R) (cover : A∪B=R) (apart : Disjoint A B)
    (paths : ∀ c,∃ x∈A,∃ y∈B,Walk (Joined g w c) x y)
    (budget : w.card+(R.card-2)≤(2*n+2)/3) : Exact g ((2*n+2)/3) :=
  exact_of_upper (upper_if_two (by omega) g w R A B legal reach cover apart paths budget)
    (fun _ => odd_lower hn g)

#print axioms two_group_reduction
#print axioms exact_if_two
end WildCuts.OneExtra
