import MotifSum30
import MotifRows30

namespace WildSieve.Thirty.Graph
open Finset Motifs
local instance (priority := 2000) momentEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq

abbrev Deck := Layout (univ : Finset V)
noncomputable def hits (F : Factor V C) (D : Deck) := (family F).filter (·⊆D.val)
noncomputable def shortBad (F : Factor V C) := (family F).biUnion event

theorem hit_iff (F : Factor V C) (D : Deck) : (hits F D).Nonempty ↔ D∈shortBad F := by
  classical
  simp only [hits,shortBad,Finset.filter_nonempty_iff,mem_biUnion,event,extensions,mem_filter,mem_univ,true_and]

private theorem layout_size (D : Deck) : D.val.card=10 := by
  have h := D.property.1.card_vertices
  rw [D.property.2,card_univ,Fintype.card_fin] at h
  omega

private theorem point (F : Factor V C) (D : Deck) :
    12*(if D∈shortBad F then 1 else 0) +
      (∑ v∈pairPool (hits F D),pairCost (pairKey v)) ≤
    12*(hits F D).card+orderedThree (hits F D) coupon := by
  classical
  let H := hits F D
  have size (e : Pattern) (he : e∈H) := pattern_size (mem_filter.mp he).1
  have fits (e : Pattern) (he : e∈H) := (mem_filter.mp he).2
  have small : D.val.card≤10 := (layout_size D).le
  have graph := of_decide_eq_true (graph_on_blocks D.val small H size fits)
  have per (J : Finset Pattern) (h : J∈H.powersetCard 3) :=
    three_covered small J (fun e he => size e ((mem_powersetCard.mp h).1 he))
      (fun e he => fits e ((mem_powersetCard.mp h).1 he)) (mem_powersetCard.mp h).2
  have rebate := sum_le_sum per
  rw [←mul_sum,sum_triples] at rebate
  change 2*EdgeDeletion.bill tripleCredit 3 H≤orderedThree H coupon at rebate
  rw [sum_pairs]
  change 12*(if D∈shortBad F then 1 else 0)+2*EdgeDeletion.bill pairCost 2 H≤_
  by_cases bad : D∈shortBad F
  · rw [if_pos bad]
    have many : 0<H.card := card_pos.mpr ((hit_iff F D).mpr bad)
    have inequality := graph.resolve_left (Nat.ne_of_gt many)
    change _ ≤ 12*H.card+orderedThree H coupon
    omega
  · have empty : hits F D=∅ := not_nonempty_iff_eq_empty.mp (fun h => bad ((hit_iff F D).mp h))
    simp [H,empty,bad,EdgeDeletion.bill,orderedThree]

private theorem exchange {α β : Type} [Fintype α] [DecidableEq α]
    (pool : Finset β) (events : β → Finset α) (w : β → Nat) :
    (∑ D : α,∑ v∈pool.filter (fun v => D∈events v),w v)=∑ v∈pool,w v*(events v).card := by
  classical
  simp only [sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  rw [←sum_filter,sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_comm]
  simp

private theorem hit_event (F : Factor V C) (D : Deck) :
    hits F D=(family F).filter (fun p => D∈event p) := by
  classical ext p; simp [hits,event,extensions]

private theorem hit_pairs (F : Factor V C) (D : Deck) :
    pairPool (hits F D)=(pairPool (family F)).filter (fun v => D∈event (v.1∪v.2)) := by
  classical
  ext v
  simp only [pairPool,hits,mem_filter,mem_product,event,extensions,mem_univ,true_and,union_subset_iff]
  tauto

private theorem hit_triples (F : Factor V C) (D : Deck) :
    triplePool (hits F D)=(triplePool (family F)).filter (fun v => D∈event (v.1∪v.2.1∪v.2.2)) := by
  classical
  ext v
  simp only [triplePool,hits,mem_filter,mem_product,event,extensions,mem_univ,true_and,union_subset_iff]
  tauto

private theorem first_total (F : Factor V C) : (∑ D : Deck,(hits F D).card)=10*(marks F univ).card*ways 8 := by
  classical
  have ex := exchange (family F) event (fun _ => 1)
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,mul_one,one_mul] at ex
  simp_rw [hit_event,ex]
  have each (p : Pattern) (h : p∈family F) : (event p).card=ways 8 := by
    rw [event_mass (pattern_mem.mp h).1,pattern_size h]
  rw [sum_congr rfl each,sum_const,nsmul_eq_mul,Nat.cast_id,pattern_card]

private theorem pair_charge {F : Factor V C} {P Q : Pattern} (p : P∈family F) (q : Q∈family F) (ne : P≠Q) :
    pairCost ({P,Q} : Finset Pattern)*(event (P∪Q)).card=
    charge (Separate P Q) (5*ways 6)+charge (Wedge P Q) (4*ways 7) := by
  classical
  have nodesEq : nodes ({P,Q} : Finset Pattern)=P∪Q := by ext X; simp [nodes]
  by_cases sep : Separate P Q
  · have d := (separate_iff _ _).mp sep
    have dis := blocks_disjoint (pattern_mem.mp p).1 d
    have no : ¬Wedge P Q := fun h => h.2.2 dis
    have sz : (P∪Q).card=4 := by rw [card_union_of_disjoint dis,pattern_size p,pattern_size q]
    have ok := (pattern_mem.mp p).1.combine (pattern_mem.mp q).1 d
    simp only [pairCost,nodesEq,sz,if_true,event_mass ok,charge,if_pos sep,if_neg no,add_zero]
  by_cases w : Wedge P Q
  · have sz := wedge_size p q w
    simp only [pairCost,nodesEq,sz,event_mass w.2.1,charge,if_neg sep,if_pos w,zero_add]
    decide
  · have zero : ¬Triples (P∪Q) := fun ok => w ⟨ne,ok,fun d => sep ((separate_iff _ _).mpr (supports_disjoint ok d))⟩
    simp [charge,sep,w,event_empty zero]

private theorem different_if_separate {F : Factor V C} {P Q : Pattern} (p : P∈family F) (s : Separate P Q) : Q≠P := by
  rintro rfl
  have empty := disjoint_self.mp ((separate_iff _ _).mp s)
  have n := (mark_mem.mp (pattern_mem.mp p).2).2.1
  rw [empty] at n
  contradiction

private theorem pair_tallies (F : Factor V C) (a b : Nat) :
    (∑ v∈pairPool (family F),(charge (Separate v.1 v.2) a+charge (Wedge v.1 v.2) b))=
      (wide F).card*a+(touching F).card*b := by
  classical
  have sep : (pairPool (family F)).filter (fun v => Separate v.1 v.2)=wide F := by
    ext v
    simp only [pairPool,wide,mem_filter,mem_product]
    exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,different_if_separate h.1.1 h.2⟩,h.2⟩⟩
  have adj : (pairPool (family F)).filter (fun v => Wedge v.1 v.2)=touching F := by
    ext v
    simp only [pairPool,touching,mem_filter,mem_product]
    exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,h.2.1.symm⟩,h.2⟩⟩
  simp only [charge,sum_add_distrib,←sum_filter,sep,adj,sum_const,nsmul_eq_mul,Nat.cast_id]

private theorem second_total (F : Factor V C) :
    (∑ D : Deck, ∑ v∈pairPool (hits F D),pairCost (pairKey v)) =
    (wide F).card*(5*ways 6)+(touching F).card*(4*ways 7) := by
  classical
  simp_rw [hit_pairs]
  rw [exchange,←pair_tallies]
  apply sum_congr rfl
  intro v hv
  obtain ⟨h,ne⟩ := mem_filter.mp hv
  exact pair_charge (mem_product.mp h).1 (mem_product.mp h).2 ne.symm

private theorem pairs_as_sum {α : Type} [DecidableEq α] (S : Finset α) (f : α → α → Nat) :
    (∑ v∈pairPool S,f v.1 v.2)=∑ P∈S,∑ Q∈S.erase P,f P Q := by
  classical simp only [pairPool,sum_filter,sum_product,←filter_ne',sum_filter]

private theorem third_total (F : Factor V C) :
    (∑ D : Deck,orderedThree (hits F D) coupon) ≤ (wide F).card*(9420*ways 4)+
      (touching F).card*(44400*ways 5+153*ways 6) := by
  classical
  simp_rw [←sum_pool,hit_triples]
  rw [exchange,←pair_tallies,pairs_as_sum (family F) (fun P Q =>
    charge (Separate P Q) (9420*ways 4)+charge (Wedge P Q) (44400*ways 5+153*ways 6))]
  change (∑ v∈triplePool (family F),coupon v.1 v.2.1 v.2.2*(event (v.1∪v.2.1∪v.2.2)).card)≤_
  rw [sum_pool (family F) (fun P Q R => coupon P Q R*(event (P∪Q∪R)).card)]
  unfold orderedThree
  apply sum_le_sum
  intro P p
  apply sum_le_sum
  intro Q q
  apply le_trans _ (motif_row p (mem_of_mem_erase q) (mem_erase.mp q).1.symm)
  exact sum_le_sum_of_subset_of_nonneg ((erase_subset _ _).trans (erase_subset _ _)) (fun _ _ _ => Nat.zero_le _)

theorem short_count (F : Factor V C) :
    12*(shortBad F).card+((wide F).card*(5*ways 6)+(touching F).card*(4*ways 7)) ≤
    12*(10*(marks F univ).card*ways 8) +
      ((wide F).card*(9420*ways 4)+(touching F).card*(44400*ways 5+153*ways 6)) := by
  classical
  have sum := sum_le_sum (s:=univ) (fun D _ => point F D)
  rw [sum_add_distrib,sum_add_distrib,←mul_sum,←mul_sum,first_total,second_total] at sum
  have size : (∑ D : Deck,if D∈shortBad F then 1 else 0)=(shortBad F).card := by simp
  rw [size] at sum
  exact sum.trans (Nat.add_le_add_left (third_total F) _)

#print axioms short_count
end WildSieve.Thirty.Graph
