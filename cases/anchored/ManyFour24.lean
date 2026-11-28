import Anchor24
import LocalFrames

namespace WildAnchor.K24.FourCycles
open Finset WildExact

set_option maxRecDepth 10000
set_option maxHeartbeats 0

/-- The two group names attached to each of the twelve anchor edges. -/
private def groups (x : Point 12) : Fin 8 :=
  if x.2 then (#[7,3,0,1,2,0,7,2,3,1,6,5] : Array (Fin 8))[x.1.val]!
  else (#[7,3,5,4,6,4,6,5,2,0,4,1] : Array (Fin 8))[x.1.val]!

private def root : Point 12 := (2,true)
private def weights : Nat × Nat → Nat
  | (0,6) => 66355200
  | (0,9) => 1114767360
  | (1,4) => 27095040
  | (1,7) => 154828800
  | (2,2) => 12902400
  | (2,5) => 44236800
  | (3,3) => 34836480
  | (3,6) => 26542080
  | (4,1) => 42577920
  | (4,4) => 28311552
  | (5,2) => 66355200
  | (5,5) => 29491200
  | (6,0) => 165888000
  | (6,3) => 79626240
  | (7,1) => 402554880
  | (8,2) => 495452160
  | (9,0) => 5573836800
  | (10,1) => 14863564800
  | _ => 0

private def base := 83271352320
private def charge := 4782587904

private theorem table : ∀ i j : Fin 13,
    sideCharge groups (groups root) (i.val,j.val)=weights (i.val,j.val) := by native_decide
private theorem anchor : ∀ a : Sides 8 (groups root),∃ i,(groupSide groups a i).1≠(groupSide groups a i).2 := by
  native_decide

private theorem bounds : (cycleLists 12 2 12).all (fun cs => decide
    (quickBill 12 weights cs≤base+charge*(6-cs.count 2)))=true := by native_decide

/-- Twenty-two companions can make at most 132 alternating four-cycles
with an anchor. A shortfall of at most 27 still gives sixteen wild edges. -/
theorem exact (g : Coloring 24 23) (a : Fin 23)
    (cs : {c : Fin 23 // c≠a} → List Nat) (ord : ∀ c,OrderedCycles 12 2 (cs c))
    (charts : ∀ c,∃ w,AlternatingChart g a c.val (cyclePerm 12 (cs c)) w)
    (deficit : (∑ c,(6-(cs c).count 2))≤27) : Exact g 16 := by
  obtain ⟨c,hc⟩ : ∃ c : Fin 23,c≠a := by
    by_cases h : a=0
    · exact ⟨1,h ▸ (by decide)⟩
    · exact ⟨0,Ne.symm h⟩
  obtain ⟨e,frame⟩ := frame_of_charts g a _ ⟨c,hc⟩ charts
  have each c := of_decide_eq_true (List.all_eq_true.mp bounds _ (cycle_member (by decide) (ord c)))
  have total := sum_le_sum (s:=univ) (fun c _ => each c)
  have size : Fintype.card {c : Fin 23 // c≠a}=22 := by simp
  simp only [sum_add_distrib,sum_const,card_univ,size,nsmul_eq_mul,←mul_sum] at total
  have budget : (∑ c,quickBill 12 weights (cs c))<(12 : Nat).factorial*2^12 := by
    have bound := Nat.mul_le_mul_left charge deficit
    have room : 22*base+charge*27<(12 : Nat).factorial*2^12 := by decide
    omega
  have upper := template_sum g a e cs frame groups root weights table anchor budget
  have cost : starCost groups=16 := by native_decide
  exact exact_of_upper (cost ▸ upper) (fun _ => even_lower (by decide) g)

#print axioms exact
end WildAnchor.K24.FourCycles
