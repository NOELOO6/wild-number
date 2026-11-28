import TripleNeighbors
import Mathlib.Tactic.Ring

namespace WildSieve.SixCounts
open Finset
variable {n k : Nat}
local notation "V" => Fin n
local notation "C" => Fin k
local instance (priority := 2000) wedgeVertexEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq

noncomputable def wedgesAt (F : Factor V C) (A : Finset V) :=
  ((neighbors F A) ×ˢ (neighbors F A)).filter (fun p => Disjoint p.1 p.2)

private theorem point_tally (F : Factor V C) (A : Finset V) :
    (∑ B∈neighbors F A,∑ D∈neighbors F A,(B∩D).card)=
      ∑ x∈Aᶜ,(incidence F A x)^2 := by
  classical
  let N := neighbors F A
  have count (B D : Finset V) (hb : B∈N) :
      (B∩D).card=∑ x∈Aᶜ,if x∈B then (if x∈D then 1 else 0) else 0 := by
    rw [←sum_filter,←sum_filter,sum_const]
    have eq : (Aᶜ.filter (fun x => x∈B)).filter (fun x => x∈D)=B∩D := by
      ext x; simp only [mem_filter,mem_inter]
      exact ⟨fun h => ⟨h.1.2,h.2⟩,fun h => ⟨⟨(neigh_mem.mp hb).1 h.1,h.1⟩,h.2⟩⟩
    simp [eq]
  have row (x : V) : (∑ B∈N,if x∈B then 1 else 0)=incidence F A x := by
    simp [incidence,N]
  have mid (B : Finset V) (hb : B∈N) : (∑ D∈N,(B∩D).card)=
      ∑ x∈Aᶜ,if x∈B then incidence F A x else 0 := by
    simp_rw [fun D => count B D hb]
    rw [sum_comm]
    apply sum_congr rfl
    intro x _
    by_cases h : x∈B <;> simp [h,row]
  change (∑ B∈N,_) = _
  rw [sum_congr rfl mid,sum_comm]
  apply sum_congr rfl
  intro x _
  rw [←sum_filter,sum_const,nsmul_eq_mul,pow_two]
  rfl

/-- Linearizing the square around a degree cap d keeps a loss of at most
2d+2 per deleted neighbor. -/
theorem wedge_lower_at (F : Factor V C) (A : Finset V) (d sq base : Nat)
    (degree : (neighbors F A).card≤d) (square : ∑ x∈Aᶜ,(incidence F A x)^2≤sq)
    (table : ∀ i : Fin (d+1), base+(2*d+2)*i.val+sq≤i.val*i.val+2*i.val+(2*d+2)*d) :
    base+(2*d+2)*(neighbors F A).card≤(wedgesAt F A).card+(2*d+2)*d := by
  classical
  let N := neighbors F A
  have point (B : Finset V) (hb : B∈N) (D : Finset V) :
      1+(if D=B then 2 else 0)≤(if Disjoint B D then 1 else 0)+(B∩D).card := by
    by_cases eq : D=B
    · subst D
      simp only [ite_true,inter_self,(neigh_mem.mp hb).2.1,eq_self]
      omega
    · rw [if_neg eq,add_zero]
      by_cases dis : Disjoint B D
      · rw [if_pos dis]; omega
      · rw [if_neg dis,zero_add]
        exact card_pos.mpr (not_disjoint_iff_nonempty_inter.mp dis)
  have rows := sum_le_sum (s:=N) (fun B hb => sum_le_sum (s:=N) (fun D _ => point B hb D))
  have lhs : (∑ B∈N,∑ D∈N,(1+(if D=B then 2 else 0)))=N.card*N.card+2*N.card := by
    simp [sum_add_distrib,Nat.mul_add,Nat.mul_comm]
  have count : (∑ B∈N,∑ D∈N,if Disjoint B D then 1 else 0)=(wedgesAt F A).card := by
    rw [←sum_product']
    simp [wedgesAt,N]
  rw [lhs] at rows
  simp only [sum_add_distrib,count,point_tally,N] at rows
  have h := table ⟨(neighbors F A).card,by omega⟩
  dsimp only at h
  omega

private theorem degree_by_marks (F : Factor V C) (A : Finset V) (s : A.card=3) :
    (neighbors F A).card=((marks F univ).filter (fun Q => A⊆Q)).card := by
  classical
  let N := neighbors F A
  have eq : N.image (fun B => A∪B)=(marks F univ).filter (fun Q => A⊆Q) := by
    ext Q
    constructor
    · rintro h
      obtain ⟨B,hb,rfl⟩ := mem_image.mp h
      obtain ⟨dis,sz,cl⟩ := neigh_mem.mp hb
      have sep : Disjoint A B := disjoint_left.mpr (fun _ ha hb => mem_compl.mp (dis hb) ha)
      exact mem_filter.mpr ⟨mark_mem.mpr ⟨subset_univ _,by rw [card_union_of_disjoint sep,s,sz],cl⟩,subset_union_left⟩
    · intro h
      obtain ⟨hq,sub⟩ := mem_filter.mp h
      obtain ⟨_,sz,cl⟩ := mark_mem.mp hq
      have fit : Q \ A ∈ N := neigh_mem.mpr ⟨fun _ hx => mem_compl.mpr (mem_sdiff.mp hx).2,
        by rw [card_sdiff sub,sz,s],by rwa [union_sdiff_of_subset sub]⟩
      exact mem_image.mpr ⟨Q \ A,fit,union_sdiff_of_subset sub⟩
  have recover (B : Finset V) (h : B∈N) : (A∪B) \ A=B := by
    ext x
    have no (hx : x∈B) := mem_compl.mp ((neigh_mem.mp h).1 hx)
    simp only [mem_sdiff,mem_union]
    tauto
  have inj : Set.InjOn (fun B => A∪B) N := by
    intro B hb D hd e
    exact (recover B hb).symm.trans ((congrArg (· \ A) e).trans (recover D hd))
  rw [←eq,card_image_of_injOn inj]

theorem total_degree (F : Factor V C) :
    (∑ A∈triples n,(neighbors F A).card)=20*(marks F univ).card := by
  classical
  let H := marks F univ
  calc
    _ = ∑ A∈triples n,∑ Q∈H,if A⊆Q then 1 else 0 := by
      apply sum_congr rfl
      intro A h
      rw [degree_by_marks F A (triple_mem.mp h)]
      simp [H]
    _ = _ := by
      rw [sum_comm]
      have per (Q : Finset V) (h : Q∈H) : (∑ A∈triples n,if A⊆Q then 1 else 0)=20 := by
        rw [←sum_filter,sum_const]
        have eq : (triples n).filter (fun A => A⊆Q)=Q.powersetCard 3 := by
          ext A; simp [triple_mem,and_comm]
        rw [eq,card_powersetCard,(mark_mem.mp h).2.1]
        decide
      rw [sum_congr rfl per,sum_const,nsmul_eq_mul,Nat.mul_comm]
      rfl

theorem all_wedges_lower (F : Factor V C) (d sq base : Nat)
    (degree : ∀ A : Finset V, A.card=3 → (neighbors F A).card≤d)
    (square : ∀ A : Finset V, A.card=3 → ∑ x∈Aᶜ,(incidence F A x)^2≤sq)
    (table : ∀ i : Fin (d+1), base+(2*d+2)*i.val+sq≤i.val*i.val+2*i.val+(2*d+2)*d)
    (balanced : n.choose 3*d=20*(k*(n/2).choose 3)) :
    n.choose 3*base ≤ (∑ A∈triples n,(wedgesAt F A).card)+(2*d+2)*20*defect F := by
  have rows := sum_le_sum (s:=triples n) (fun A h => wedge_lower_at F A
    d sq base (degree A (triple_mem.mp h)) (square A (triple_mem.mp h)) table)
  rw [sum_add_distrib,sum_const,←mul_sum,total_degree,sum_add_distrib,sum_const,num_triples] at rows
  simp only [nsmul_eq_mul,Nat.cast_id] at rows
  have hh := (full_defect F).2
  have eq : n.choose 3*((2*d+2)*d)=(2*d+2)*(20*(marks F univ).card)+(2*d+2)*20*defect F := by
    calc
      _ = (2*d+2)*(n.choose 3*d) := by ring
      _ = (2*d+2)*(20*((marks F univ).card+defect F)) := by rw [balanced,hh]
      _ = _ := by ring
  rw [eq] at rows
  omega

end WildSieve.SixCounts
