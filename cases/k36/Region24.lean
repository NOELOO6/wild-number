import Multiplicity36
import MixedSixes
import LongCredit
import OverlapCredit

namespace WildSieve.ThirtySix
open Finset
local instance (priority := 2000) regionVertexEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq

private theorem mixed_region (F : Factor V C) (S W : Finset V) (s : S.card=6) (w : W.card=18) :
    ((marks F (S∪W)).filter (fun Q => (Q∩S).card=3)).card≤1000 := by
  classical
  let row (c : C) := (candidates F c ∅ (S∪W) 6).filter (fun Q => (Q∩S).card=3)
  have sub : (marks F (S∪W)).filter (fun Q => (Q∩S).card=3) ⊆ univ.biUnion row := by
    intro Q h
    obtain ⟨c,hc⟩ := side_mem.mp (mem_filter.mp h).1
    exact mem_biUnion.mpr ⟨c,mem_univ _,mem_filter.mpr ⟨hc,(mem_filter.mp h).2⟩⟩
  have per (c : C) : (row c).card≤20+20*Inside F c S := by
    have b := mixed_six_color F c S W s (row c) (by
      intro Q h
      obtain ⟨hc,th⟩ := mem_filter.mp h
      obtain ⟨q,sz,cl⟩ := candidate_mem.mp hc
      exact ⟨q,sz,th,by simpa using cl⟩)
    have ss := (inside_window F c S).2
    have ww := (inside_window F c W).2
    rw [s] at ss
    rw [w] at ww
    have small : ∀ a : Fin 4,∀ b : Fin 10,
        (6-2*a.val).choose 3+a.val*(6-2*a.val)*b.val ≤ 20+20*a.val := by decide
    exact b.trans (small ⟨Inside F c S,by omega⟩ ⟨Inside F c W,by omega⟩)
  have high := (card_le_card sub).trans (card_biUnion_le.trans (sum_le_sum (s:=univ) (fun c _ => per c)))
  rw [sum_add_distrib,sum_const,←mul_sum,sum_inside,s] at high
  exact high

/-- Two different six-sets in a 24-point region can both be sealed only
when disjoint or when their intersection is one of the layout triples. -/
private theorem double24 (X S Q : Finset V) (sz : X.card=24) (su : S⊆X) (qu : Q⊆X)
    (s : S.card=6) (q : Q.card=6) (diff : Q≠S) :
    (localSeal X S∩localSeal X Q).card≤
      (if Q⊆X \ S then 100*ways 4 else 0)+(if (Q∩S).card=3 then ways 5 else 0) := by
  classical
  let W := X \ S
  have ws : W.card=18 := by rw [show W=X \ S from rfl,card_sdiff su,sz,s]
  by_cases dis : Disjoint S Q
  · have qw : Q⊆X \ S := fun x hx => mem_sdiff.mpr ⟨qu hx,fun hs => disjoint_left.mp dis hs hx⟩
    rw [equal_joint X S Q 2 2 4 su qu dis s q (by rw [sz,s,q]),if_pos qw]
    have eq : ways 2*ways 2*ways 4=100*ways 4 := by decide
    omega
  by_cases three : (Q∩S).card=3
  · let I := S∩Q
    let R := Q \ S
    have isz : I.card=3 := by simpa [I,inter_comm] using three
    have rsz : R.card=3 := by dsimp [R];have h := card_sdiff_add_card_inter Q S;omega
    have wsub : R⊆W := fun x hx => mem_sdiff.mpr ⟨qu (mem_sdiff.mp hx).1,(mem_sdiff.mp hx).2⟩
    have bound := split_upper X S su (localSeal X S∩localSeal X Q) (localSeal S I) (localSeal W R)
      inter_subset_left (fun P h => by
        obtain ⟨hi,hr⟩ := seal_parts (mem_inter.mp h).1 (mem_inter.mp h).2
        exact ⟨(seal_glue_left X S I su P inter_subset_left).mp hi,(seal_glue_right X S R su P wsub).mp hr⟩)
    rw [local_seal_card S I 1 1 inter_subset_left isz (by rw [s,isz]),
      local_seal_card W R 1 5 wsub rsz (by rw [ws,rsz])] at bound
    rw [if_pos three]
    change _≤ways 5 at bound
    omega
  have zero : (localSeal X S∩localSeal X Q).card=0 := by
    apply card_eq_zero.mpr (eq_empty_iff_forall_not_mem.mpr ?_)
    intro D h
    have div := intersect_sealed (mem_inter.mp h).2 (mem_inter.mp h).1
    have pos := card_pos.mpr (not_disjoint_iff_nonempty_inter.mp (fun o => dis o.symm) : (Q∩S).Nonempty)
    have cap := card_le_card (inter_subset_left : Q∩S ⊆ Q)
    have ne : (Q∩S).card≠6 := by
      intro eq
      have a := eq_of_subset_of_card_le (inter_subset_left : Q∩S⊆Q) (by omega)
      have b := eq_of_subset_of_card_le (inter_subset_right : Q∩S⊆S) (by omega)
      exact diff (a.symm.trans b)
    omega
  simp [zero]

def regionalSingle := 10*ways 6
def regionalDouble := 1428*(100*ways 4)+1000*ways 5
def regionalCredit := 4*regionalSingle-regionalDouble

private theorem local_neighborhood (F : Factor V C) (X S : Finset V) (size : X.card=24)
    (hs : S∈marks F X) : (∑ Q∈(marks F X).erase S,(localSeal X S∩localSeal X Q).card)≤regionalDouble := by
  classical
  obtain ⟨sub,s,_⟩ := mark_mem.mp hs
  let G := (marks F X).erase S
  let W := X \ S
  have w : W.card=18 := by rw [show W=X \ S from rfl,card_sdiff sub,size,s]
  have cover : S∪W=X := union_sdiff_of_subset sub
  have each (Q : Finset V) (hw : Q∈G) := double24 X S Q size sub
    (mark_mem.mp (mem_erase.mp hw).2).1 s (mark_mem.mp (mem_erase.mp hw).2).2.1 (mem_erase.mp hw).1
  have sum := sum_le_sum each
  have left : (G.filter (fun Q => Q⊆W)).card≤1428 := by
    apply (card_le_card (show G.filter (fun Q => Q⊆W) ⊆ marks F W from ?_)).trans
      ((marks_le_labeled F W).trans (labels_le_18 F W w))
    intro Q h
    exact mark_mem.mpr ⟨(mem_filter.mp h).2,(mark_mem.mp (mem_erase.mp (mem_filter.mp h).1).2).2⟩
  have right : (G.filter (fun Q => (Q∩S).card=3)).card≤1000 := by
    apply (card_le_card (show G.filter (fun Q => (Q∩S).card=3) ⊆
      (marks F (S∪W)).filter (fun Q => (Q∩S).card=3) from ?_)).trans (mixed_region F S W s w)
    rw [cover]
    exact fun Q h => mem_filter.mpr ⟨(mem_erase.mp (mem_filter.mp h).1).2,(mem_filter.mp h).2⟩
  change (∑ Q∈G,_)≤∑ Q∈G,((if Q⊆W then 100*ways 4 else 0)+(if (Q∩S).card=3 then ways 5 else 0)) at sum
  rw [sum_add_distrib,←sum_filter,←sum_filter,sum_const,sum_const,nsmul_eq_mul,nsmul_eq_mul] at sum
  exact sum.trans (Nat.add_le_add (Nat.mul_le_mul_right _ left) (Nat.mul_le_mul_right _ right))

/-- In a color-closed 24-set, marks of every color exclude local subdivisions. -/
theorem region_credit (F : Factor V C) (X : Finset V) (size : X.card=24) (c : C) (cl : Closed (F.f c) X) :
    6*(noSix F X).card+1956*regionalCredit≤6*ways 8+defect F*regionalCredit := by
  classical
  let H := marks F X
  let E := localSeal X
  have sizeE (S : Finset V) (hs : S∈H) : (E S).card=regionalSingle :=
    local_seal_card X S 2 6 (mark_mem.mp hs).1 (mark_mem.mp hs).2.1 (by rw [size,(mark_mem.mp hs).2.1])
  have law := coverage_four H E
  rw [sum_congr rfl sizeE,sum_const,nsmul_eq_mul] at law
  have two := sum_le_sum (s:=H) (fun S h => local_neighborhood F X S size h)
  rw [sum_const,nsmul_eq_mul] at two
  have lower := labels_ge_24 F X size c cl
  have loss := localized_defect F X
  change labeled F X+(marks F univ).card≤labeled F univ+H.card at loss
  have total : labeled F univ=28560 := all_labels F
  rw [total] at loss
  have full := (full_defect F).2
  change (marks F univ).card+defect F=28560 at full
  have n : 1956≤H.card+defect F := by omega
  have no : noSix F X=(H.biUnion E)ᶜ := by ext D; simp [noSix_mem,H,E]
  have deck : (noSix F X).card+(H.biUnion E).card=ways 8 := by
    rw [no,card_compl,card_layout 8 X size]
    have cap := (H.biUnion E).card_le_univ
    rw [card_layout 8 X size] at cap
    omega
  have credit := Nat.mul_le_mul_right regionalCredit n
  rw [Nat.add_mul] at credit
  change (∑ S∈H,∑ Q∈H.erase S,(E S∩E Q).card)≤H.card*regionalDouble at two
  change 4*(H.card*regionalSingle)≤6*(H.biUnion E).card+_ at law
  norm_num [regionalCredit,regionalSingle,regionalDouble,ways,Nat.fast_choose] at credit law two deck ⊢
  omega

end WildSieve.ThirtySix
