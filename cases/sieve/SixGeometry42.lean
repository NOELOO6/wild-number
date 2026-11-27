import MixedSixes
namespace WildSieve.FortyTwo
open Finset
abbrev V := Fin 42
abbrev C := Fin 41
local instance (priority := 2000) vertexEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq

private theorem full_pairs (F : Factor V C) (c : C) : Inside F c univ=21 := by
  have n := closed_size (F.invol c) (F.moving c) (show Closed (F.f c) univ from fun _ _ => mem_univ _)
  rw [card_univ,Fintype.card_fin] at n
  change 42=2*Inside F c univ at n
  omega

theorem total_marks (F : Factor V C) : (marks F univ).card≤54530 := by
  have bound := card_biUnion_le (s:=(univ:Finset C)) (t:=fun c => candidates F c ∅ univ 6)
  change (marks F univ).card≤_ at bound
  simpa only [show 6=2*3 by decide,candidate_pairs,full_pairs,sum_const,card_univ,Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_id] using bound

private theorem inside_window (F : Factor V C) (c : C) (U : Finset V) :
    U.card-21≤Inside F c U ∧ 2*Inside F c U≤U.card := by
  have a := ends_bound (F.invol c) U
  have b := free_pair_size (F.invol c) (F.moving c) U
  rw [card_compl,Fintype.card_fin] at b
  have cap := U.card_le_univ
  simp only [Fintype.card_fin] at cap
  have full := full_pairs F c
  have cc := ends_bound (F.invol c) Uᶜ
  rw [card_compl,Fintype.card_fin] at cc
  have side := free_pair_size (F.invol c) (F.moving c) Uᶜ
  rw [compl_compl,card_compl,Fintype.card_fin] at side
  change _≤(lowerEnds (F.f c) U).card ∧ _≤_
  exact ⟨by omega,a⟩

/-- A marked six can be paired with many disjoint marks. Any loss of
distinct labels is charged against the full coloring's duplicate count. -/
theorem disjoint_lower (F : Factor V C) (S : Finset V) (sz : S.card=6) :
    20230+(marks F univ).card≤54530+(marks F Sᶜ).card := by
  have sc : Sᶜ.card=36 := by rw [card_compl,Fintype.card_fin,sz]
  have cmp : ∀ i : Fin 22,105*i.val≤i.val.choose 3+1120 := by decide
  have per (c) : 105*Inside F c Sᶜ≤(Inside F c Sᶜ).choose 3+1120 := by
    have h := (inside_window F c Sᶜ).2
    rw [sc] at h
    exact cmp ⟨Inside F c Sᶜ,by omega⟩
  have all := sum_le_sum (s:=univ) (fun c _ => per c)
  rw [←mul_sum,sum_inside,sc,sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at all
  have loc := localized_defect F Sᶜ
  simp only [full_pairs,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at loc
  change 66150≤(∑ c,(Inside F c Sᶜ).choose 3)+45920 at all
  change _≤54530+_ at loc
  omega

/-- Bound labeled six-point sets entirely inside a specified thirty points. -/
theorem in_thirty (F : Factor V C) (W : Finset V) (sz : W.card=30) : (marks F W).card≤7525 := by
  have cmp : ∀ i : Fin 16,9≤i.val → 6*i.val.choose 3+2835≤371*i.val := by decide
  have per (c) : 6*(Inside F c W).choose 3+2835≤371*Inside F c W := by
    obtain ⟨lo,hi⟩ := inside_window F c W
    rw [sz] at lo hi
    exact cmp ⟨Inside F c W,by omega⟩ lo
  have all := sum_le_sum (s:=univ) (fun c _ => per c)
  rw [sum_add_distrib,←mul_sum,←mul_sum,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,sum_inside,sz] at all
  have bound := card_biUnion_le (s:=(univ:Finset C)) (t:=fun c => candidates F c ∅ W 6)
  change (marks F W).card≤_ at bound
  simp only [show 6=2*3 by decide,candidate_pairs] at bound
  change 6*(∑ c,(Inside F c W).choose 3)+116235≤161385 at all
  omega

/-- Bound marks using three points on each side of a 6 + 30 split. -/
theorem meet_three (F : Factor V C) (S W : Finset V) (s : S.card=6) (w : W.card=30) :
    ((marks F (S∪W)).filter (fun Q => (Q∩S).card=3)).card≤1480 := by
  classical
  let row (c : C) := (candidates F c ∅ (S∪W) 6).filter (fun Q => (Q∩S).card=3)
  have sub : (marks F (S∪W)).filter (fun Q => (Q∩S).card=3) ⊆ univ.biUnion row := by
    intro Q h
    obtain ⟨c,hc⟩ := side_mem.mp (mem_filter.mp h).1
    exact mem_biUnion.mpr ⟨c,mem_univ _,mem_filter.mpr ⟨hc,(mem_filter.mp h).2⟩⟩
  have per (c) : (row c).card≤20+44*Inside F c S := by
    have b := mixed_six_color F c S W s (row c) (by
      intro Q h
      obtain ⟨hc,th⟩ := mem_filter.mp h
      obtain ⟨q,sz,cl⟩ := candidate_mem.mp hc
      exact ⟨q,sz,th,by simpa using cl⟩)
    have ss := (inside_window F c S).2
    have ww := (inside_window F c W).2
    rw [s] at ss
    rw [w] at ww
    have small : ∀ a : Fin 4,∀ b : Fin 16,
        (6-2*a.val).choose 3+a.val*(6-2*a.val)*b.val ≤ 20+44*a.val := by decide
    exact b.trans (small ⟨Inside F c S,by omega⟩ ⟨Inside F c W,by omega⟩)
  have high := (card_le_card sub).trans (card_biUnion_le.trans (sum_le_sum (s:=univ) (fun c _ => per c)))
  rw [sum_add_distrib,sum_const,←mul_sum,sum_inside,s,card_univ,Fintype.card_fin,nsmul_eq_mul] at high
  exact high
end WildSieve.FortyTwo
