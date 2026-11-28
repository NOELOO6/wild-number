import PairCutCheck
import LocalFrames

namespace WildAnchor.K30
open Finset WildExact
set_option maxRecDepth 50000
set_option maxHeartbeats 0

private theorem fast_eq (next : Equiv.Perm (Fin 15)) : fastPairBill next=pairBill next := by
  unfold fastPairBill pairBill
  apply sum_congr rfl
  intro k _
  have atPoint (i : Fin 15) : (Array.ofFn fun j : Fin 15 => next.symm j)[i.val]! = next.symm i := by
    have h : i.val<(Array.ofFn fun j : Fin 15 => next.symm j).size := by simp
    simp only [getElem!_pos (c:=Array.ofFn fun j : Fin 15 => next.symm j) (i:=i.val) h,Array.getElem_ofFn]
  simp only [atPoint]
  rfl

/-- Number of potentially losing shuffles after crediting two simultaneous
disjoint closed pairs of groups. -/
def correctedBill (cs : List Nat) := singleBill cs-fastPairBill (cyclePerm 15 cs)

private theorem loss_le_bill (cs : List Nat) :
    (binaryLoss (cyclePerm 15 cs)).card≤correctedBill cs := by
  let next := cyclePerm 15 cs
  have less := corrected_bound next
  rw [show (∑ a : Side,∑ b : Mask 15,price (groupSide tag a) (row next (bits b)))=singleBill cs
    from singleBill_eq cs] at less
  have credit := pairBill_le next
  unfold correctedBill
  rw [fast_eq]
  change (binaryLoss next).card≤singleBill cs-pairBill next
  omega

private theorem anchorOK : ∀ i : Side,∃ j,(groupSide tag i j).1≠(groupSide tag i j).2 := by native_decide

/-- The actual cycle profile of the anchor can be used even when a
companion makes an alternating four-cycle. -/
theorem exact_of_cycle_budget (g : Coloring 30 29) (a : Fin 29)
    (cs : {c : Fin 29 // c≠a} → List Nat)
    (charts : ∀ c,∃ w,AlternatingChart g a c.val (cyclePerm 15 (cs c)) w)
    (small : (∑ c,correctedBill (cs c)) < (15 : Nat).factorial*2^15) : Exact g 20 := by
  obtain ⟨d,ne⟩ : ∃ d : Fin 29,d≠a := by
    by_cases h : a=0
    · exact ⟨1,h ▸ (by decide)⟩
    · exact ⟨0,Ne.symm h⟩
  obtain ⟨e,frame⟩ := frame_of_charts g a _ ⟨d,ne⟩ charts
  have upper : Upper g (starCost tag) := by
    apply anchored_upper_of_selection g a e _ frame tag root (groupSide tag) bits all_bits
      (all_groupSides tag root) anchorOK
    intro coords
    apply choose_from_losses _ _ coords (fun c => correctedBill (cs c))
    · exact fun c => loss_le_bill (cs c)
    · simpa only [Fintype.card_fin] using small
  have cost : starCost tag=20 := by native_decide
  exact exact_of_upper (cost ▸ upper) (fun _ => even_lower (by decide) g)

private theorem per_color (cs : List Nat) (ord : OrderedCycles 15 3 cs) : correctedBill cs≤budget := by
  have ok := Bool.or_eq_true_iff.mp (List.all_eq_true.mp sufficient cs (cycle_member (by decide) ord))
  rcases ok with cheap|save
  · exact (Nat.sub_le ..).trans (of_decide_eq_true cheap)
  · have h : singleBill cs≤budget+fastPairBill (cyclePerm 15 cs) := of_decide_eq_true save
    unfold correctedBill
    omega

/-- Twenty wild edges suffice whenever one anchor has no alternating
four-cycle with any other color. Each chart uses the ordered lengths of
the alternating cycles in units of anchor edges. -/
theorem exact_no_four (g : Coloring 30 29) (a : Fin 29)
    (cs : {c : Fin 29 // c≠a} → List Nat) (ord : ∀ c,OrderedCycles 15 3 (cs c))
    (charts : ∀ c,∃ w,AlternatingChart g a c.val (cyclePerm 15 (cs c)) w) : Exact g 20 := by
  apply exact_of_cycle_budget g a cs charts
  have total := sum_le_sum (s:=univ) (fun c _ => per_color (cs c) (ord c))
  have size : Fintype.card {c : Fin 29 // c≠a}=28 := by simp
  simp only [sum_const,card_univ,size,nsmul_eq_mul] at total
  exact total.trans_lt (by decide)

/-- In particular, it suffices that the anchor and each companion form
a Hamiltonian alternating cycle. -/
theorem exact_hamiltonian_anchor (g : Coloring 30 29) (a : Fin 29)
    (walks : ∀ c : {c : Fin 29 // c≠a},∃ w,AlternatingChart g a c.val (cyclePerm 15 [15]) w) :
    Exact g 20 :=
  exact_no_four g a (fun _ => [15]) (fun _ => show OrderedCycles 15 3 [15] from by simp [OrderedCycles]) walks

#print axioms exact_no_four
#print axioms exact_hamiltonian_anchor
end WildAnchor.K30
