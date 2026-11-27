import SixGeometry42
import LayoutSplit
namespace WildSieve.FortyTwo
open Finset
set_option maxHeartbeats 3000000
local instance (priority := 2000) tripleVertexEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq
noncomputable def hit (T : Finset V) := localSeal (univ:Finset V) T

theorem double_card (T S : Finset V) (t : T.card=6) (s : S.card=6) (d : Disjoint T S) :
    (hit T∩hit S).card=100*ways 10 := by
  exact equal_joint univ T S 2 2 10 (subset_univ _) (subset_univ _) d t s (by simp [t,s])

private theorem triple_card (T S Q : Finset V) (t : T.card=6) (s : S.card=6) (q : Q.card=6)
    (ds : Disjoint T S) (dq : Disjoint T Q) (diff : Q≠S) :
    let W := (univ \ T) \ S
    (hit T∩hit S∩hit Q).card≤(if Q⊆W then 1000*ways 8 else 0)+
      (if (Q∩S).card=3 then 10*ways 9 else 0) := by
  classical
  let U := (univ:Finset V) \ T
  let W := U \ S
  have su : S⊆U := fun x hx => mem_sdiff.mpr ⟨mem_univ _,fun ht => disjoint_left.mp ds ht hx⟩
  have qu : Q⊆U := fun x hx => mem_sdiff.mpr ⟨mem_univ _,fun ht => disjoint_left.mp dq ht hx⟩
  have us : U.card=36 := by dsimp [U];rw [card_sdiff (subset_univ _),card_univ,Fintype.card_fin,t]
  have ws : W.card=30 := by rw [show W=U \ S from rfl,card_sdiff su,us,s]
  have cut := drop_cut univ T (subset_univ _) (hit T∩hit S∩hit Q)
    (localSeal U S∩localSeal U Q) (inter_subset_left.trans inter_subset_left) (fun P => by
      simp only [mem_inter,hit,seal_glue,seal_glue_right _ T S _ P su,seal_glue_right _ T Q _ P qu,true_and,U])
  rw [card_layout 2 T t] at cut
  change (hit T∩hit S∩hit Q).card≤(if Q⊆W then _ else _)+(if _ then _ else _)
  rw [cut]
  by_cases dis : Disjoint S Q
  · have qw : Q⊆W := fun x hx => mem_sdiff.mpr ⟨qu hx,fun hs => disjoint_left.mp dis hs hx⟩
    have eq := equal_joint U S Q 2 2 8 su qu dis s q (by rw [us,s,q])
    rw [eq,if_pos qw]
    have h : ways 2*(ways 2*ways 2*ways 8)=1000*ways 8 := by decide
    omega
  by_cases three : (Q∩S).card=3
  · let I := S∩Q
    let R := Q \ S
    have isz : I.card=3 := by simpa [I,inter_comm] using three
    have rsz : R.card=3 := by dsimp [R];have h := card_sdiff_add_card_inter Q S;omega
    have wsub : R⊆W := fun x hx => mem_sdiff.mpr ⟨qu (mem_sdiff.mp hx).1,(mem_sdiff.mp hx).2⟩
    have bound := split_upper U S su (localSeal U S∩localSeal U Q) (localSeal S I) (localSeal W R)
      inter_subset_left (fun P h => by
        obtain ⟨hi,hr⟩ := seal_parts (mem_inter.mp h).1 (mem_inter.mp h).2
        exact ⟨(seal_glue_left U S I su P inter_subset_left).mp hi,(seal_glue_right U S R su P wsub).mp hr⟩)
    rw [local_seal_card S I 1 1 inter_subset_left isz (by rw [s,isz]),
      local_seal_card W R 1 9 wsub rsz (by rw [ws,rsz])] at bound
    have b := Nat.mul_le_mul_left (ways 2) bound
    change ways 2*_≤10*ways 9 at b
    rw [if_pos three]
    omega
  have zero : (localSeal U S∩localSeal U Q).card=0 := by
    apply card_eq_zero.mpr (eq_empty_iff_forall_not_mem.mpr ?_)
    intro D h
    have div := intersect_sealed (mem_inter.mp h).2 (mem_inter.mp h).1
    have pos := card_pos.mpr (not_disjoint_iff_nonempty_inter.mp (fun o => dis o.symm) : (Q∩S).Nonempty)
    have cap := card_le_card (inter_subset_left : Q∩S⊆Q)
    have ne : (Q∩S).card≠6 := by
      intro eq
      have a := eq_of_subset_of_card_le (inter_subset_left : Q∩S⊆Q) (by omega)
      have b := eq_of_subset_of_card_le (inter_subset_right : Q∩S⊆S) (by omega)
      exact diff (a.symm.trans b)
    omega
  simp [zero]

theorem triple_budget (F : Factor V C) (T S : Finset V) (t : T.card=6)
    (hs : S∈marks F Tᶜ) :
    (∑ Q∈(marks F Tᶜ).erase S,(hit T∩hit S∩hit Q).card)≤
      7525*(1000*ways 8)+1480*(10*ways 9) := by
  classical
  obtain ⟨st,s,_⟩ := mark_mem.mp hs
  let G := (marks F Tᶜ).erase S
  let W := (univ \ T) \ S
  have eqU : (univ:Finset V) \ T=Tᶜ := by ext; simp
  have sw : S∪W=Tᶜ := by dsimp [W];rw [eqU,union_sdiff_of_subset st]
  have ws : W.card=30 := by
    dsimp [W];rw [eqU,card_sdiff st,card_compl,Fintype.card_fin,t,s]
  have dis (Q : Finset V) (h : Q⊆Tᶜ) : Disjoint T Q :=
    disjoint_left.mpr (fun _ ht hq => mem_compl.mp (h hq) ht)
  have per (Q) (hq : Q∈G) := triple_card T S Q t s (mark_mem.mp (mem_erase.mp hq).2).2.1
    (dis S st) (dis Q (mark_mem.mp (mem_erase.mp hq).2).1) (mem_erase.mp hq).1
  have all := sum_le_sum per
  let L := G.filter (fun Q => Q⊆W)
  let R := G.filter (fun Q => (Q∩S).card=3)
  have lc : L.card≤7525 := by
    apply (card_le_card (show L⊆marks F W from ?_)).trans (in_thirty F W ws)
    intro Q h
    exact mark_mem.mpr ⟨(mem_filter.mp h).2,(mark_mem.mp (mem_erase.mp (mem_filter.mp h).1).2).2⟩
  have rc : R.card≤1480 := by
    apply (card_le_card (show R⊆(marks F (S∪W)).filter (fun Q => (Q∩S).card=3) from ?_)).trans (meet_three F S W s ws)
    rw [sw]
    exact fun Q h => mem_filter.mpr ⟨(mem_erase.mp (mem_filter.mp h).1).2,(mem_filter.mp h).2⟩
  change (∑ Q∈G,_)≤∑ Q∈G,((if Q⊆W then _ else _)+(if (Q∩S).card=3 then _ else _)) at all
  rw [sum_add_distrib,←sum_filter,←sum_filter,sum_const,sum_const,nsmul_eq_mul,nsmul_eq_mul] at all
  exact all.trans (Nat.add_le_add (Nat.mul_le_mul_right _ lc) (Nat.mul_le_mul_right _ rc))

end WildSieve.FortyTwo
