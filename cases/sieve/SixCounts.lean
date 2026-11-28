import MatchingSixes

namespace WildSieve.SixCounts
open Finset
variable {n k : Nat}
local notation "V" => Fin n
local notation "C" => Fin k
local instance (priority := 2000) vertexEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq

/-- The number of six-sets, counted once for each color closing them. -/
def labeled (F : Factor V C) (U : Finset V) := ∑ c,(Inside F c U).choose 3

theorem full_pairs (F : Factor V C) (c : C) : Inside F c univ=n/2 := by
  have h := closed_size (F.invol c) (F.moving c)
    (show Closed (F.f c) univ from fun _ _ => mem_univ _)
  change (univ : Finset V).card=2*Inside F c univ at h
  rw [card_univ,Fintype.card_fin] at h
  omega

theorem all_labels (F : Factor V C) : labeled F univ=k*(n/2).choose 3 := by
  simp [labeled,full_pairs]

theorem inside_window (F : Factor V C) (c : C) (U : Finset V) :
    U.card-n/2≤Inside F c U ∧ 2*Inside F c U≤U.card := by
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

theorem chord (F : Factor V C) (U : Finset V)
    (u w a b : Nat) (size : U.card=u)
    (table : ∀ i : Fin (n/2+1), u-n/2≤i.val → 2*i.val≤u → w*i.val.choose 3+a≤b*i.val) :
    w*labeled F U+k*a≤b*u.choose 2 := by
  have per (c : C) : w*(Inside F c U).choose 3+a≤b*Inside F c U := by
    obtain ⟨lo,hi⟩ := inside_window F c U
    rw [size] at lo hi
    have cap := U.card_le_univ
    rw [size] at cap
    simp only [Fintype.card_fin] at cap
    exact table ⟨Inside F c U,by omega⟩ lo hi
  have all := sum_le_sum (s:=univ) (fun c _ => per c)
  simpa only [labeled,sum_add_distrib,←mul_sum,sum_const,card_univ,Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_id,sum_inside,size] using all

theorem tangent (F : Factor V C) (U : Finset V) (u a b bonus : Nat)
    (size : U.card=u) (c₀ : C) (closed : Closed (F.f c₀) U)
    (line : ∀ i : Fin (n/2+1), a*i.val≤i.val.choose 3+b)
    (improve : a*(u/2)+bonus≤(u/2).choose 3+b) :
    a*u.choose 2+bonus≤labeled F U+k*b := by
  classical
  have cc := closed_size (F.invol c₀) (F.moving c₀) closed
  change U.card=2*Inside F c₀ U at cc
  rw [size] at cc
  have per (c : C) : a*Inside F c U + (if c=c₀ then bonus else 0)≤(Inside F c U).choose 3+b := by
    by_cases eq : c=c₀
    · subst c
      simpa only [if_pos rfl,show Inside F c₀ U=u/2 by omega] using improve
    · rw [if_neg eq,add_zero]
      have h := (inside_window F c U).2
      have cap := U.card_le_univ
      simp only [Fintype.card_fin] at cap
      exact line ⟨Inside F c U,by omega⟩
  have all := sum_le_sum (s:=univ) (fun c _ => per c)
  simpa [labeled,sum_add_distrib,←mul_sum,sum_inside,size] using all

noncomputable def owners (F : Factor V C) (Q : Finset V) : Finset C := by
  classical exact univ.filter fun c => Closed (F.f c) Q

theorem owner_mem {F : Factor V C} {Q : Finset V} {c : C} :
    c∈owners F Q ↔ Closed (F.f c) Q := by classical simp [owners]

noncomputable def extra (F : Factor V C) (Q : Finset V) := (owners F Q).card-1
noncomputable def defect (F : Factor V C) := (k*(n/2).choose 3)-(marks F univ).card

theorem mark_tally (F : Factor V C) (U : Finset V) :
    (∑ Q∈marks F U,(owners F Q).card)=labeled F U := by
  classical
  have col (c : C) : (marks F U).filter (fun Q => c∈owners F Q)=candidates F c ∅ U 6 := by
    ext Q
    simp only [mem_filter,mark_mem,owner_mem,candidate_mem,empty_union]
    constructor
    · rintro ⟨⟨sub,sz,_⟩,cl⟩
      exact ⟨sub,sz,cl⟩
    · rintro ⟨sub,sz,cl⟩
      exact ⟨⟨sub,sz,c,cl⟩,cl⟩
  have row (Q : Finset V) : (owners F Q).card=∑ c : C,if c∈owners F Q then 1 else 0 := by simp
  simp_rw [row]
  rw [sum_comm]
  unfold labeled
  apply sum_congr rfl
  intro c _
  rw [←sum_filter, sum_const, nsmul_eq_mul, mul_one,col,candidate_pairs F c U 3]
  rfl

theorem extra_tally (F : Factor V C) (U : Finset V) :
    (∑ Q∈marks F U,extra F Q)+(marks F U).card=labeled F U := by
  classical
  have row (Q : Finset V) (mem : Q∈marks F U) : extra F Q+1=(owners F Q).card := by
    obtain ⟨c,cl⟩ := (mark_mem.mp mem).2.2
    have pos := card_pos.mpr (show (owners F Q).Nonempty from ⟨c,owner_mem.mpr cl⟩)
    unfold extra
    omega
  simpa [sum_add_distrib,mark_tally] using sum_congr rfl row

theorem marks_le_labeled (F : Factor V C) (U : Finset V) : (marks F U).card≤labeled F U := by
  have h := extra_tally F U
  omega

theorem full_defect (F : Factor V C) :
    (∑ Q∈marks F univ,extra F Q)=defect F ∧ (marks F univ).card+defect F=(k*(n/2).choose 3) := by
  have h := extra_tally F univ
  rw [all_labels] at h
  unfold defect
  omega

theorem closed_complement (F : Factor V C) (c : C) (U : Finset V) (h : Closed (F.f c) U) :
    Closed (F.f c) Uᶜ := by
  intro x hx
  exact mem_compl.mpr fun e => mem_compl.mp hx (F.invol c x ▸ h _ e)

/-- Each deleted color label on Q is charged only to marked sets disjoint
from Q. This keeps its cost below the complementary region upper bound. -/
theorem disjoint_count (F : Factor V C) (lower upper : Nat)
    (hi : ∀ U : Finset V, U.card=n-6 → labeled F U≤upper)
    (lo : ∀ U : Finset V, U.card=n-6 → ∀ c : C, Closed (F.f c) U → lower≤labeled F U) :
    (marks F univ).card*lower≤(∑ T∈marks F univ,(marks F Tᶜ).card)+upper*defect F := by
  classical
  let H := marks F univ
  have sz {T : Finset V} (h : T∈H) : Tᶜ.card=n-6 := by
    rw [card_compl,Fintype.card_fin,(mark_mem.mp h).2.1]
  have per (T : Finset V) (h : T∈H) : lower≤(marks F Tᶜ).card+∑ Q∈marks F Tᶜ,extra F Q := by
    obtain ⟨c,cl⟩ := (mark_mem.mp h).2.2
    rw [add_comm,extra_tally]
    exact lo _ (sz h) c (closed_complement F c T cl)
  have flip (T Q : Finset V) : Q⊆Tᶜ ↔ T⊆Qᶜ := by
    constructor <;> intro h x hx <;> exact mem_compl.mpr (fun y => mem_compl.mp (h y) hx)
  have exchange : (∑ T∈H,∑ Q∈marks F Tᶜ,extra F Q)=
      ∑ Q∈H,(marks F Qᶜ).card*extra F Q := by
    calc
      _ = ∑ T∈H,∑ Q∈H,if T⊆Qᶜ then extra F Q else 0 := by
        apply sum_congr rfl
        intro T _
        rw [marks_filter,sum_filter]
        exact sum_congr rfl (fun Q _ => by
          by_cases h : Q⊆Tᶜ
          · simp [h,(flip T Q).mp h]
          · have den : ¬T⊆Qᶜ := fun v => h ((flip T Q).mpr v)
            simp [h,den])
      _ = _ := by
        rw [sum_comm]
        apply sum_congr rfl
        intro Q _
        rw [←sum_filter,sum_const,nsmul_eq_mul,marks_filter]
        rfl
  have cost := sum_le_sum (s:=H) (fun Q h => Nat.mul_le_mul_right (extra F Q)
    ((marks_le_labeled F Qᶜ).trans (hi _ (sz h))))
  rw [←mul_sum,(full_defect F).1] at cost
  have all := sum_le_sum (s:=H) per
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,sum_add_distrib,exchange] at all
  exact all.trans (Nat.add_le_add_left cost _)

end WildSieve.SixCounts
