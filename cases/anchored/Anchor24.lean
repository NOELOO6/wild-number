import CycleLists
namespace WildAnchor.K24
open Finset WildExact
set_option maxRecDepth 10000
set_option maxHeartbeats 0

/-- Each column gives the two group labels of an anchor edge. -/
def tag (x : Point 12) : Fin 8 :=
  if x.2 then (#[0,7,3,6,3,5,2,4,7,6,5,7] : Array (Fin 8))[x.1.val]!
  else (#[0,2,1,2,3,5,0,4,4,6,1,1] : Array (Fin 8))[x.1.val]!
def root : Point 12 := (1,true)

private def weights : Nat × Nat → Nat
  | (0,9) => 1114767360
  | (1,7) => 185794560
  | (2,5) => 40550400
  | (2,8) => 165150720
  | (3,3) => 9953280
  | (3,6) => 132710400
  | (4,1) => 3870720
  | (4,4) => 81395712
  | (5,2) => 36864000
  | (5,5) => 176947200
  | (6,0) => 33177600
  | (6,3) => 291962880
  | (7,1) => 185794560
  | (7,4) => 495452160
  | (8,2) => 2312110080
  | (9,0) => 2229534720
  | (10,1) => 37158912000
  | _ => 0

private def base := 87429611520
private def charge := 16783441920

private theorem table : ∀ i j : Fin 13,sideCharge tag (tag root) (i.val,j.val)=weights (i.val,j.val) := by native_decide
private theorem anchor : ∀ i : Sides 8 (tag root),∃ j,(groupSide tag i j).1≠(groupSide tag i j).2 := by native_decide
private theorem bounds : (cycleLists 12 2 12).all (fun cs => decide
    (quickBill 12 weights cs ≤ base+charge*cs.count 2))=true := by native_decide

/-- Exact for any ordinary coloring with an anchor having at most two alternating four-cycles in total.
Cycle sizes in its frame are measured in anchor edges. -/
theorem exact (g : Coloring 24 23) (a : Fin 23) (e : Point 12 ≃ Fin 24)
    (cs : {c : Fin 23 // c≠a} → List Nat) (ord : ∀ c,OrderedCycles 12 2 (cs c))
    (frame : InFrame g a e (fun c => cyclePerm 12 (cs c)))
    (short : (∑ c,(cs c).count 2)≤2) : Exact g 16 := by
  have size : Fintype.card {c : Fin 23 // c≠a}=22 := by simp
  have each c := of_decide_eq_true (List.all_eq_true.mp bounds _ (cycle_member (by decide) (ord c)))
  have total := sum_le_sum (s:=(univ : Finset {c : Fin 23 // c≠a})) (fun c _ => each c)
  simp only [sum_add_distrib,sum_const,card_univ,size,nsmul_eq_mul,←mul_sum] at total
  have budget : (∑ c,quickBill 12 weights (cs c))<(12 : Nat).factorial*2^12 := by
    have price := Nat.mul_le_mul_left charge short
    have limit : 22*base+charge*2 < (12 : Nat).factorial*2^12 := by decide
    omega
  have upper := template_sum g a e cs frame tag root weights table anchor budget
  have sz : starCost tag=16 := by native_decide
  exact exact_of_upper (sz ▸ upper) (fun _ => even_lower (by decide) g)

#print axioms exact
end WildAnchor.K24
