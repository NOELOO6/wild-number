import TripleCounts
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace WildSieve.TripleIncidence
open Finset
variable {V : Type} [Fintype V] [DecidableEq V]

def within (H : Finset (Finset V)) (U : Finset V) := H.filter (·⊆U)
def throughPair (H : Finset (Finset V)) (P : Finset V) := H.filter (P⊆·)

def PairBound (H : Finset (Finset V)) (k : Nat) := ∀ P : Finset V, P.card=2 → (throughPair H P).card≤k

private theorem exchange {α β : Type} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (p : α → β → Prop) [∀ a b, Decidable (p a b)] :
    (∑ a∈A,(B.filter (p a)).card)=∑ b∈B,(A.filter (fun a => p a b)).card := by
  simp only [card_filter]
  rw [sum_comm]

omit [Fintype V] in
/-- Count the three vertex pairs in each retained triple, then count by pair. -/
theorem within_bound (H : Finset (Finset V)) (size : ∀ A∈H,A.card=3) (k)
    (cap : PairBound H k) (U : Finset V) : 3*(within H U).card≤k*U.card.choose 2 := by
  classical
  let K := within H U
  let pairs := U.powersetCard 2
  have row (T) (h : T∈K) : (pairs.filter (·⊆T)).card=3 := by
    have sub := (mem_filter.mp h).2
    have eq : pairs.filter (·⊆T)=T.powersetCard 2 := by
      ext P
      simp only [pairs,mem_filter,mem_powersetCard]
      exact ⟨fun q => ⟨q.2,q.1.2⟩,fun q => ⟨⟨q.1.trans sub,q.2⟩,q.1⟩⟩
    rw [eq,card_powersetCard,size _ (mem_filter.mp h).1]
    decide
  have col (P) (hp : P∈pairs) : (K.filter (P⊆·)).card≤k := by
    apply le_trans _ (cap P (mem_powersetCard.mp hp).2)
    exact card_le_card (fun _ h => mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp h).1).1,(mem_filter.mp h).2⟩)
  have e := exchange K pairs (fun T P => P⊆T)
  rw [sum_congr rfl row,sum_const] at e
  have b := sum_le_sum col
  rw [sum_const,card_powersetCard] at b
  simpa only [nsmul_eq_mul,Nat.cast_id,Nat.mul_comm] using e.le.trans b

theorem vertex_bound (H : Finset (Finset V)) (size : ∀ A∈H,A.card=3) (k)
    (cap : PairBound H k) (z : V) :
    2*(H.filter (z∈·)).card ≤ k*(Fintype.card V-1) := by
  classical
  let K := H.filter (z∈·)
  let pts := (univ : Finset V).erase z
  have row (T) (h : T∈K) : (pts.filter (·∈T)).card=2 := by
    have eq : pts.filter (·∈T)=T.erase z := by ext; simp [pts]
    rw [eq,card_erase_of_mem (mem_filter.mp h).2,size _ (mem_filter.mp h).1]
  have col (y) (hy : y∈pts) : (K.filter (fun T => y∈T)).card≤k := by
    apply le_trans _ (cap {y,z} (by simp [(mem_erase.mp hy).1]))
    apply card_le_card
    intro T h
    obtain ⟨a,b⟩ := mem_filter.mp h
    obtain ⟨inH,zin⟩ := mem_filter.mp a
    exact mem_filter.mpr ⟨inH,insert_subset b (singleton_subset_iff.mpr zin)⟩
  have e := exchange K pts (fun T y => y∈T)
  rw [sum_congr rfl row,sum_const] at e
  have b := sum_le_sum col
  rw [sum_const] at b
  simpa only [pts,card_erase_of_mem (mem_univ z),card_univ,nsmul_eq_mul,Nat.cast_id,Nat.mul_comm]
    using e.le.trans b

/-- A forbidden triple accounts three times for itself when its three
vertex neighborhoods are added. -/
theorem disjoint_lower (H : Finset (Finset V)) (size : ∀ A∈H,A.card=3) (k)
    (cap : PairBound H k) {T : Finset V} (ht : T∈H) :
    H.card+2 ≤ (within H Tᶜ).card+3*(k*(Fintype.card V-1)/2) := by
  classical
  let around (x : V) := (H.erase T).filter (x∈·)
  let d := k*(Fintype.card V-1)/2
  have cost (x) (hx : x∈T) : (around x).card+1≤d := by
    have eq : around x=(H.filter (x∈·)).erase T := by ext; simp [around,and_left_comm,and_assoc]
    rw [eq,card_erase_of_mem (mem_filter.mpr ⟨ht,hx⟩)]
    have pos := card_pos.mpr (show (H.filter (x∈·)).Nonempty from ⟨T,mem_filter.mpr ⟨ht,hx⟩⟩)
    have b := vertex_bound H size k cap x
    dsimp [d]
    omega
  have sub : H.erase T⊆within H Tᶜ∪T.biUnion around := by
    intro A ha
    by_cases meet : ∃ x∈T,x∈A
    · obtain ⟨x,hx,ax⟩ := meet
      exact mem_union_right _ (mem_biUnion.mpr ⟨x,hx,mem_filter.mpr ⟨ha,ax⟩⟩)
    · exact mem_union_left _ (mem_filter.mpr ⟨(mem_erase.mp ha).2,
        fun x hx => mem_compl.mpr fun tx => meet ⟨x,tx,hx⟩⟩)
  have a := (card_le_card sub).trans (card_union_le ..)
  have b := card_biUnion_le (s:=T) (t:=around)
  have e := sum_le_sum cost
  rw [sum_add_distrib,sum_const,sum_const,size _ ht] at e
  rw [card_erase_of_mem ht] at a
  have pos := card_pos.mpr (show H.Nonempty from ⟨T,ht⟩)
  simp only [nsmul_eq_mul,Nat.cast_id,mul_one] at e
  omega

/-- Every other triple meeting T contains exactly two pairs across the cut T | Tᶜ. -/
theorem crossing_disjoint (H : Finset (Finset V)) (size : ∀ A∈H,A.card=3) (k)
    (cap : PairBound H k) {T : Finset V} (ht : T∈H) :
    H.card ≤ (within H Tᶜ).card+1+3*(Fintype.card V-3)*k/2 := by
  classical
  let K := (H.erase T).filter (fun A => ¬Disjoint A T)
  let C := T ×ˢ Tᶜ
  let hits (A : Finset V) (q : V × V) := q.1∈A ∧ q.2∈A
  have row (A) (ha : A∈K) : (C.filter (hits A)).card=2 := by
    obtain ⟨er,meet⟩ := mem_filter.mp ha
    have split : C.filter (hits A)=(A∩T) ×ˢ (A \ T) := by ext q; simp [C,hits,and_assoc,and_left_comm,and_comm]
    have pos : 0<(A∩T).card := card_pos.mpr (not_disjoint_iff_nonempty_inter.mp meet)
    have bound : (A∩T).card<3 := by
      by_contra! bad
      have eq : A∩T=A := eq_of_subset_of_card_le inter_subset_left (by simpa [size A (mem_erase.mp er).2] using bad)
      have sub : A⊆T := by rw [←eq]; exact inter_subset_right
      exact (mem_erase.mp er).1 (eq_of_subset_of_card_le sub (by rw [size _ ht,size _ (mem_erase.mp er).2]))
    rw [split,card_product]
    have parts := card_sdiff_add_card_inter A T
    rw [size A (mem_erase.mp er).2] at parts
    have cases : (A∩T).card=1 ∨ (A∩T).card=2 := by omega
    rcases cases with one|two
    · rw [one] at parts ⊢; omega
    · rw [two] at parts ⊢; omega
  have col (q) (hq : q∈C) : (K.filter (fun A => hits A q)).card≤k := by
    obtain ⟨x,y⟩ := mem_product.mp hq
    have ne : q.1≠q.2 := fun eq => mem_compl.mp y (eq ▸ x)
    apply le_trans _ (cap {q.1,q.2} (by simp [ne]))
    apply card_le_card
    intro A h
    obtain ⟨hk,h1,h2⟩ := mem_filter.mp h
    exact mem_filter.mpr ⟨(mem_erase.mp (mem_filter.mp hk).1).2,insert_subset h1 (singleton_subset_iff.mpr h2)⟩
  have e := exchange K C hits
  rw [sum_congr rfl row,sum_const] at e
  have b := sum_le_sum col
  rw [sum_const,show C.card=3*(Fintype.card V-3) by simp [C,card_compl,size _ ht]] at b
  have cover : H⊆(within H Tᶜ ∪ K)∪{T} := by
    intro A ha
    by_cases eq : A=T
    · simp [eq]
    by_cases d : Disjoint A T
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨ha,fun x hx => mem_compl.mpr (disjoint_left.mp d hx)⟩))
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨mem_erase.mpr ⟨eq,ha⟩,d⟩))
  have u := (card_le_card cover).trans (card_union_le ..)
  have v := card_union_le (within H Tᶜ) K
  simp only [nsmul_eq_mul,Nat.cast_id,card_singleton] at e b u
  omega

end WildSieve.TripleIncidence
