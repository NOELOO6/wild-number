import SixCounts
import Mathlib.Tactic.Linarith

namespace WildSieve.SixCounts
open Finset
variable {n k : Nat}
local notation "V" => Fin n
local notation "C" => Fin k
local instance (priority := 2000) neighborVertexEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq

def triples (m : Nat) : Finset (Finset (Fin m)) := (univ : Finset (Fin m)).powersetCard 3

theorem triple_mem {A : Finset V} : A∈triples n ↔ A.card=3 := by simp [triples]
theorem num_triples : (triples n).card=n.choose 3 := by rw [triples,card_powersetCard,card_univ,Fintype.card_fin]

/-- A neighbor B makes the union of its triple and A closed in this color. -/
noncomputable def colorNeighbors (F : Factor V C) (A : Finset V) (c : C) :=
  candidates F c A Aᶜ 3
noncomputable def neighbors (F : Factor V C) (A : Finset V) :=
  (univ : Finset C).biUnion (colorNeighbors F A)

theorem neigh_mem {F : Factor V C} {A B : Finset V} : B∈neighbors F A ↔
    B⊆Aᶜ ∧ B.card=3 ∧ ∃ c,Closed (F.f c) (A∪B) := by
  classical
  simp only [neighbors,mem_biUnion,mem_univ,true_and,colorNeighbors,candidate_mem]
  constructor
  · rintro ⟨c,h,s,cl⟩; exact ⟨h,s,c,cl⟩
  · rintro ⟨h,s,c,cl⟩; exact ⟨c,h,s,cl⟩

def forcedOut (F : Factor V C) (A : Finset V) (c : C) := forced (F.f c) A A

theorem strip {F : Factor V C} {A B : Finset V} {c : C} (h : B∈colorNeighbors F A c) :
    B⊆Aᶜ ∧ B.card=3 ∧ forcedOut F A c⊆B ∧ Closed (F.f c) (B \ forcedOut F A c) := by
  obtain ⟨sub,sz,cl⟩ := candidate_mem.mp h
  exact ⟨sub,sz,strip_fixed (F.invol c) (Subset.refl _)
    (disjoint_left.mpr (fun _ hb ha => mem_compl.mp (sub hb) ha)) cl⟩

theorem forced_size (F : Factor V C) (A : Finset V) (size : A.card=3) (c : C) :
    (forcedOut F A c).card=3-2*Inside F c A := by
  simpa only [forcedOut,Inside,size] using external_size (F.invol c) (F.moving c) A

theorem inside_le_one (F : Factor V C) (A : Finset V) (size : A.card=3) (c : C) :
    Inside F c A≤1 := by
  have h := (inside_window F c A).2
  omega

theorem forced_sub (F : Factor V C) (A : Finset V) (c : C) : forcedOut F A c⊆Aᶜ :=
  fun _ h => mem_compl.mpr (mem_sdiff.mp h).2

theorem color_degree (F : Factor V C) (A : Finset V) (size : A.card=3) (c : C) :
    (colorNeighbors F A c).card≤1+(n/2-3)*Inside F c A := by
  let R := forcedOut F A c
  have count := count_free (F.invol c) (F.moving c) Aᶜ R (colorNeighbors F A c) 3
    (fun _ h => strip h)
  have rsize := forced_size F A size c
  have hi := inside_le_one F A size c
  rcases (show Inside F c A=0 ∨ Inside F c A=1 by omega) with h|h
  · change R.card=_ at rsize
    rw [h] at rsize ⊢
    simpa [rsize] using count
  · change R.card=_ at rsize
    rw [h] at rsize ⊢
    have cap := ends_bound (F.invol c) (Aᶜ \ R)
    rw [card_sdiff (forced_sub F A c),card_compl,size,Fintype.card_fin,rsize] at cap
    simp only [rsize] at count
    change (colorNeighbors F A c).card≤(lowerEnds (F.f c) (Aᶜ \ R)).card.choose 1 at count
    rw [Nat.choose_one_right] at count
    omega

theorem degree_le (F : Factor V C) (A : Finset V) (size : A.card=3) : (neighbors F A).card≤k+3*(n/2-3) := by
  have total := sum_le_sum (s:=univ) (fun c _ => color_degree F A size c)
  have cap := (card_biUnion_le (s:=(univ:Finset C)) (t:=colorNeighbors F A)).trans total
  simpa [neighbors,sum_add_distrib,←mul_sum,sum_inside,size,Nat.mul_comm] using cap

private theorem through (hn : 8≤n) (F : Factor V C) (A : Finset V) (size : A.card=3) (c : C) (x : V) :
    ((colorNeighbors F A c).filter (fun B => x∈B)).card ≤
      Inside F c A+(if x∈forcedOut F A c then 1+(n/2-4)*Inside F c A else 0) := by
  classical
  let S := (colorNeighbors F A c).filter (fun B => x∈B)
  let R := forcedOut F A c
  by_cases force : x∈R
  · have h := (card_le_card (filter_subset _ _ : S⊆colorNeighbors F A c)).trans (color_degree F A size c)
    change S.card≤_ + (if x∈R then _ else _)
    rw [if_pos force]
    change S.card≤_ at h
    have cap := inside_le_one F A size c
    rcases (show Inside F c A=0 ∨ Inside F c A=1 by omega) with z|z <;> rw [z] at h ⊢ <;> simp only [Nat.mul_zero,Nat.mul_one] at h ⊢ <;> omega
  · have one := count_through_pair (F.invol c) (F.moving c) Aᶜ R S 3 x (fun B h => by
      obtain ⟨hb,hx⟩ := mem_filter.mp h
      obtain ⟨bs,sz,sub,cl⟩ := strip hb
      exact ⟨bs,sz,sub,cl,mem_sdiff.mpr ⟨hx,force⟩⟩)
    have hi := inside_le_one F A size c
    have rs := forced_size F A size c
    change S.card≤_ + (if x∈R then _ else _)
    rw [if_neg force,add_zero]
    by_cases non : Inside F c A=0
    · have empty : S=∅ := by
        apply eq_empty_iff_forall_not_mem.mpr
        intro B h
        obtain ⟨hb,hx⟩ := mem_filter.mp h
        obtain ⟨_,sz,sub,_⟩ := strip hb
        have eq := eq_of_subset_of_card_le sub (by rw [sz,rs,non])
        exact force (show x∈forcedOut F A c from eq ▸ hx)
      simp [empty]
    · have eq : Inside F c A=1 := by omega
      rw [eq] at rs ⊢
      change R.card=_ at rs
      simpa [rs] using one



/-- Number of neighboring triples containing the specified outside vertex. -/
noncomputable def incidence (F : Factor V C) (A : Finset V) (x : V) :=
  ((neighbors F A).filter (fun B => x∈B)).card

private def bonus (F : Factor V C) (A : Finset V) (x : V) :=
  ∑ c : C,if x∈forcedOut F A c then Inside F c A else 0

private theorem bonus_total (F : Factor V C) (A : Finset V) (size : A.card=3) :
    ∑ x∈Aᶜ,bonus F A x=3 := by
  unfold bonus
  rw [sum_comm]
  have per (c : C) : (∑ x∈Aᶜ,if x∈forcedOut F A c then Inside F c A else 0)=Inside F c A := by
    rw [←sum_filter,sum_const,nsmul_eq_mul]
    have eq : Aᶜ.filter (fun x => x∈forcedOut F A c)=forcedOut F A c := by
      ext x
      simp only [mem_filter,and_iff_right_iff_imp]
      exact fun h => forced_sub F A c h
    rw [eq,forced_size F A size c]
    have h := inside_le_one F A size c
    rcases (show Inside F c A=0 ∨ Inside F c A=1 by omega) with z|z <;> rw [z] <;> decide
  simp only [per,sum_inside,size]
  decide

private theorem incidence_le (hn : 8≤n) (F : Factor V C) (A : Finset V) (size : A.card=3) (x : V) :
    incidence F A x≤6+(n/2-4)*bonus F A x := by
  classical
  let G := (univ : Finset C).filter (fun c => x∈forcedOut F A c)
  have few : G.card≤3 := by
    rw [←size]
    apply card_le_card_of_injOn (fun c => F.f c x) _ (F.unique x).injOn
    intro c hc
    obtain ⟨y,hy,eq⟩ := mem_image.mp (mem_sdiff.mp (mem_filter.mp hc).2).1
    simpa [←eq,F.invol c y] using hy
  have sub : (neighbors F A).filter (fun B => x∈B) ⊆
      (univ : Finset C).biUnion (fun c => (colorNeighbors F A c).filter (fun B => x∈B)) := by
    intro B hb
    obtain ⟨h,hx⟩ := mem_filter.mp hb
    obtain ⟨c,_,hc⟩ := mem_biUnion.mp h
    exact mem_biUnion.mpr ⟨c,mem_univ _,mem_filter.mpr ⟨hc,hx⟩⟩
  have sk := (card_le_card sub).trans (card_biUnion_le.trans (sum_le_sum (s:=univ) (fun c _ => through hn F A size c x)))
  have split (c : C) : (if x∈forcedOut F A c then 1+(n/2-4)*Inside F c A else 0)=
      (if x∈forcedOut F A c then 1 else 0)+(n/2-4)*(if x∈forcedOut F A c then Inside F c A else 0) := by
    split <;> simp_all
  simp_rw [split] at sk
  rw [sum_add_distrib,sum_add_distrib,←mul_sum,sum_inside,size] at sk
  have tally : (∑ c : C,if x∈forcedOut F A c then 1 else 0)=G.card := by simp [G]
  rw [tally] at sk
  change incidence F A x≤3+(G.card+(n/2-4)*bonus F A x) at sk
  omega

/-- A uniform square-incidence bound, with the coefficient left symbolic for reuse. -/
theorem incidence_squares (hn : 8≤n) (F : Factor V C) (A : Finset V) (size : A.card=3) :
    (∑ x∈Aᶜ,(incidence F A x)^2)≤(n-3)*36+3*(12*(n/2-4)+3*(n/2-4)^2) := by
  let z := n/2-4
  have total := bonus_total F A size
  have per (x : V) (hx : x∈Aᶜ) : (incidence F A x)^2≤36+(12*z+3*z^2)*bonus F A x := by
    have b := single_le_sum (s:=Aᶜ) (fun i _ => Nat.zero_le (bonus F A i)) hx
    rw [total] at b
    have bound := Nat.pow_le_pow_left (incidence_le hn F A size x) 2
    apply bound.trans
    change (6+z*bonus F A x)^2 ≤ _
    rcases (show bonus F A x=0 ∨ bonus F A x=1 ∨ bonus F A x=2 ∨ bonus F A x=3 by omega)
      with h|h|h|h <;> rw [h] <;> nlinarith [Nat.zero_le (z^2)]
  have all := sum_le_sum per
  rw [sum_add_distrib,sum_const,←mul_sum,total,card_compl,size,Fintype.card_fin] at all
  simpa only [nsmul_eq_mul,Nat.cast_id,Nat.mul_comm (12*z+3*z^2) 3] using all

end WildSieve.SixCounts
