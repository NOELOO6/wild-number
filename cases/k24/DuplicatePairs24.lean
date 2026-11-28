import ShortCuts24

namespace WildSieve.TwentyFour
open Finset SixCounts
local instance (priority := 2000) dupEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq
set_option maxHeartbeats 1000000

/-- Deduplicating both coordinates of a symmetric relation costs at most
twice the maximum weighted row sum for every surplus label. -/
theorem remove_repeated {α : Type} [DecidableEq α] (H : Finset α) (R : α → α → Prop) [DecidableRel R]
    (sym : ∀ a b,R a b ↔ R b a) (w : α → Nat) (pos : ∀ a∈H,0<w a) (cap : Nat)
    (rows : ∀ a∈H,(∑ b∈H.filter (R a),w b)≤cap) :
    (∑ a∈H,∑ b∈H.filter (R a),w a*w b) ≤
      (∑ a∈H,(H.filter (R a)).card) + 2*cap*(∑ a∈H,(w a-1)) := by
  let extra (a : α) := w a-1
  have split (a) (ha : a∈H) (b) (hb : b∈H.filter (R a)) :
      w a*w b=1+extra a*w b+extra b := by
    have x : extra a+1=w a := by have := pos a ha; dsimp [extra]; omega
    have y : extra b+1=w b := by have := pos b (mem_filter.mp hb).1; dsimp [extra]; omega
    calc
      _ = (extra a+1)*w b := by rw [x]
      _ = _ := by rw [Nat.add_mul,Nat.one_mul,←y]; ring
  have count (a) (ha : a∈H) : (H.filter (R a)).card≤cap := by
    apply le_trans _ (rows a ha)
    calc
      _ = ∑ _∈H.filter (R a),(1 : Nat) := by simp
      _ ≤ _ := sum_le_sum fun b hb => pos b (mem_filter.mp hb).1
  have first := sum_le_sum (s:=H) (fun a ha => Nat.mul_le_mul_left (extra a) (rows a ha))
  rw [←sum_mul] at first
  have second := sum_le_sum (s:=H) (fun a ha => Nat.mul_le_mul_right (extra a) (count a ha))
  rw [←mul_sum] at second
  have exchange : (∑ a∈H,∑ b∈H.filter (R a),extra b)=∑ b∈H,(H.filter (R b)).card*extra b := by
    simp only [sum_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro b _
    simp_rw [fun a => propext (sym a b)]
    rw [←sum_filter,sum_const,nsmul_eq_mul,Nat.cast_id]
  rw [sum_congr rfl (fun a ha => sum_congr rfl (split a ha))]
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_one,←mul_sum]
  rw [exchange]
  change _ ≤ _ + 2*cap*(∑ a∈H,extra a)
  rw [Nat.mul_comm (∑ a∈H,extra a) cap] at first
  rw [Nat.mul_assoc 2 cap]
  omega

noncomputable def partners (F : Factor V C) (r : Nat) (A : Finset V) :=
  (marks F univ).filter fun B => (A∩B).card=r

noncomputable def labeledPairs (F : Factor V C) (r : Nat) :=
  ∑ A∈marks F univ,∑ B∈partners F r A,(owners F A).card*(owners F B).card

noncomputable def plainPairs (F : Factor V C) (r : Nat) := ∑ A∈marks F univ,(partners F r A).card

private theorem labels_through (F : Factor V C) (T : Finset V) (sz : T.card=3) :
    (∑ Q∈(marks F univ).filter (T⊆·),(owners F Q).card)≤50 := by
  classical
  let H := (marks F univ).filter (T⊆·)
  have per (c : C) : (H.filter (fun Q => c∈owners F Q)).card≤(colorNeighbors F T c).card := by
    apply card_le_card_of_injOn (fun Q => Q \ T)
    · intro Q h
      obtain ⟨old,own⟩ := mem_filter.mp h
      obtain ⟨marked,sub⟩ := mem_filter.mp old
      have qs := (mark_mem.mp marked).2.1
      apply candidate_mem.mpr
      rw [union_sdiff_of_subset sub]
      exact ⟨fun _ hx => mem_compl.mpr (mem_sdiff.mp hx).2,by rw [card_sdiff sub,qs,sz],owner_mem.mp own⟩
    · intro Q h B hb eq
      have one := union_sdiff_of_subset (mem_filter.mp (mem_filter.mp h).1).2
      have two := union_sdiff_of_subset (mem_filter.mp (mem_filter.mp hb).1).2
      exact one.symm.trans ((congrArg (T∪·) eq).trans two)
  have total := sum_le_sum (s:=univ) (fun c _ => (per c).trans (color_degree F T sz c))
  simp only [sum_add_distrib,←mul_sum,sum_inside,sz,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at total
  have row (Q : Finset V) : (owners F Q).card=∑ c : C,if c∈owners F Q then 1 else 0 := by simp
  change (∑ Q∈H,_)≤_
  simp_rw [row]
  rw [sum_comm]
  simpa only [Finset.card_filter] using total

private theorem weighted_cap (F : Factor V C) (A : Finset V) (a : A∈marks F univ) (r : Nat)
    (job : r=0 ∨ r=3) : (∑ B∈partners F r A,(owners F B).card)≤if r=0 then 780 else 1000 := by
  classical
  have size := (mark_mem.mp a).2.1
  rcases job with rfl|rfl
  · have eq : partners F 0 A=marks F Aᶜ := by
      rw [marks_filter]
      ext B
      simp only [partners,mem_filter,card_eq_zero,←disjoint_iff_inter_eq_empty]
      exact and_congr_right (fun _ => ⟨fun d _ h => mem_compl.mpr (fun x => disjoint_left.mp d x h),
        fun sub => disjoint_left.mpr (fun x ax bx => mem_compl.mp (sub bx) ax)⟩)
    rw [eq,mark_tally]
    exact (complement_caps F Aᶜ).2.2 (by rw [card_compl,Fintype.card_fin,size])
  · let pool := partners F 3 A
    let w (B : Finset V) := (owners F B).card
    have per (B) (h : B∈pool) : w B≤∑ T∈A.powersetCard 3,if T⊆B then w B else 0 := by
      have mem : A∩B∈A.powersetCard 3 := mem_powersetCard.mpr ⟨inter_subset_left,(mem_filter.mp h).2⟩
      have cost := single_le_sum (f:=fun T : Finset V => if T⊆B then w B else 0)
        (fun _ _ => Nat.zero_le _) mem
      simpa only [if_pos (inter_subset_right : A∩B⊆B)] using cost
    have all := sum_le_sum per
    rw [sum_comm] at all
    have side (T) (ht : T∈A.powersetCard 3) : (∑ B∈pool,if T⊆B then w B else 0)≤50 := by
      rw [←sum_filter]
      apply le_trans _ (labels_through F T (mem_powersetCard.mp ht).2)
      apply sum_le_sum_of_subset
      intro B h
      exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp h).1).1,(mem_filter.mp h).2⟩
    apply all.trans
    simpa [card_powersetCard,size] using sum_le_sum side

/-- Short-pair penalties used in the two-color certificate. Both estimates
hold for every factorization before any averaging over triple partitions. -/
theorem corrected_pairs (F : Factor V C) (r : Nat) (job : r=0 ∨ r=3) :
    labeledPairs F r ≤ plainPairs F r+2*(if r=0 then 780 else 1000)*defect F := by
  classical
  have pos (A) (ha : A∈marks F univ) : 0<(owners F A).card := by
    obtain ⟨c,hc⟩ := (mark_mem.mp ha).2.2
    exact card_pos.mpr ⟨c,owner_mem.mpr hc⟩
  have result := remove_repeated (marks F univ) (fun A B => (A∩B).card=r)
    (fun A B => by simp only; rw [inter_comm]) (fun A => (owners F A).card) pos _ (fun A h => weighted_cap F A h r job)
  rw [←(full_defect F).1]
  exact result

#print axioms corrected_pairs
end WildSieve.TwentyFour
