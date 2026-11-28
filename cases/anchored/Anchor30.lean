import CycleLists
namespace WildAnchor.K30
open Finset WildExact
set_option maxRecDepth 10000
set_option maxHeartbeats 0

/-- Each column gives the two group labels of an anchor edge. -/
def tag (x : Point 15) : Fin 10 :=
  if x.2 then (#[0,1,2,3,4,9,9,7,7,6,6,8,8,5,9] : Array (Fin 10))[x.1.val]!
  else (#[0,1,2,3,3,4,2,1,4,5,6,7,8,0,5] : Array (Fin 10))[x.1.val]!
def root : Point 15 := (5,true)

private def weights : Nat × Nat → Nat
  | (0,9) => 133772083200
  | (0,12) => 11771943321600
  | (1,7) => 26011238400
  | (1,10) => 1248539443200
  | (2,5) => 4954521600
  | (2,8) => 217998950400
  | (2,11) => 1307993702400
  | (3,3) => 836075520
  | (3,6) => 60515942400
  | (3,9) => 535088332800
  | (4,4) => 19322634240
  | (4,7) => 225926184960
  | (5,2) => 6193152000
  | (5,5) => 127401984000
  | (5,8) => 317089382400
  | (6,3) => 68478566400
  | (6,6) => 331245158400
  | (7,1) => 39016857600
  | (7,4) => 398343536640
  | (7,7) => 416179814400
  | (8,2) => 317089382400
  | (8,5) => 871995801600
  | (9,0) => 267544166400
  | (9,3) => 2354388664320
  | (10,1) => 2497078886400
  | (10,4) => 2853804441600
  | (11,2) => 26159874048000
  | (12,0) => 35315829964800
  | (13,1) => 612141052723200
  | _ => 0

private def base := 1549526630400000
private def discount := 59289698304000

private theorem table : ∀ i j : Fin 16,sideCharge tag (tag root) (i.val,j.val)=weights (i.val,j.val) := by native_decide
private theorem anchor : ∀ i : Sides 10 (tag root),∃ j,(groupSide tag i j).1≠(groupSide tag i j).2 := by native_decide
private theorem bounds : (cycleLists 15 3 15).all (fun cs => decide
    (quickBill 15 weights cs + discount*(if 3∈cs then 1 else 0) ≤ base))=true := by native_decide

def singleBill (cs : List Nat) := quickBill 15 weights cs

theorem singleBill_eq (cs : List Nat) :
    (∑ a : Sides 10 (tag root),∑ b : Mask 15,price (groupSide tag a) (row (cyclePerm 15 cs) (bits b)))=
      singleBill cs :=
  (charge_table tag (tag root) (cyclePerm 15 cs) weights table).trans (quickBill_eq 15 weights cs).symm

/-- Exact for any ordinary coloring with an anchor having no alternating four-cycle, and at least ten other colors making a six-cycle.
Cycle sizes in its frame are measured in anchor edges. -/
theorem exact (g : Coloring 30 29) (a : Fin 29) (e : Point 15 ≃ Fin 30)
    (cs : {c : Fin 29 // c≠a} → List Nat) (ord : ∀ c,OrderedCycles 15 3 (cs c))
    (frame : InFrame g a e (fun c => cyclePerm 15 (cs c)))
    (short : 10≤(univ.filter (fun c => 3∈cs c)).card) : Exact g 20 := by
  have size : Fintype.card {c : Fin 29 // c≠a}=28 := by simp
  have each c := of_decide_eq_true (List.all_eq_true.mp bounds _ (cycle_member (by decide) (ord c)))
  have total := sum_le_sum (s:=(univ : Finset {c : Fin 29 // c≠a})) (fun c _ => each c)
  simp only [sum_add_distrib,sum_const,card_univ,size,nsmul_eq_mul,←mul_sum,sum_boole,Nat.cast_id] at total
  have budget : (∑ c,quickBill 15 weights (cs c))<(15 : Nat).factorial*2^15 := by
    have price := Nat.mul_le_mul_left discount short
    have limit : 28*base < (15 : Nat).factorial*2^15+discount*10 := by decide
    omega
  have upper := template_sum g a e cs frame tag root weights table anchor budget
  have sz : starCost tag=20 := by native_decide
  exact exact_of_upper (sz ▸ upper) (fun _ => even_lower (by decide) g)

#print axioms exact
end WildAnchor.K30
