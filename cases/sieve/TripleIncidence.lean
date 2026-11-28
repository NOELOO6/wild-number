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

/-- Count the three vertex pairs in each retained triple, then count by pair. -/
omit [Fintype V] in
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

end WildSieve.TripleIncidence
