import CycleLists
namespace WildAnchor.K36
open Finset WildExact
set_option maxRecDepth 10000
set_option maxHeartbeats 0

/-- Each column gives the two group labels of an anchor edge. -/
def tag (x : Point 18) : Fin 12 :=
  if x.2 then (#[0,1,2,3,4,9,8,8,7,10,6,10,11,11,9,5,5,10] : Array (Fin 12))[x.1.val]!
  else (#[0,1,2,3,4,7,1,7,5,8,6,6,11,9,3,2,4,0] : Array (Fin 12))[x.1.val]!
def root : Point 18 := (12,false)

private def weights : Nat × Nat → Nat
  | (1,10) => 112368549888000
  | (1,13) => 9794256843571200
  | (1,16) => 2742391916199936000
  | (2,8) => 43282700697600
  | (2,11) => 1961990553600000
  | (2,14) => 159972861778329600
  | (3,6) => 13644752486400
  | (3,9) => 462316319539200
  | (3,12) => 14691385265356800
  | (4,4) => 3745618329600
  | (4,7) => 156067430400000
  | (4,10) => 2465687037542400
  | (4,13) => 19588513687142400
  | (5,2) => 1226244096000
  | (5,5) => 66588770304000
  | (5,8) => 708694769664000
  | (5,11) => 5022695817216000
  | (6,3) => 28894769971200
  | (6,6) => 342456532992000
  | (6,9) => 2003370718003200
  | (7,1) => 18728091648000
  | (7,4) => 223488560332800
  | (7,7) => 1118691341107200
  | (8,2) => 133177540608000
  | (8,5) => 965537169408000
  | (8,8) => 1491588454809600
  | (9,0) => 134842259865600
  | (9,3) => 1027369598976000
  | (9,6) => 2157476157849600
  | (10,1) => 861492215808000
  | (10,4) => 3904004476108800
  | (10,7) => 2397195730944000
  | (11,2) => 6670767882240000
  | (11,5) => 7534043725824000
  | (12,0) => 8475799191552000
  | (12,3) => 29947823810150400
  | (13,1) => 68559797904998400
  | (13,4) => 39177027374284800
  | (14,2) => 479918585334988800
  | (15,0) => 1285496210718720000
  | (16,1) => 16454351497199616000
  | _ => 0

private def base := 48922272742558924800
private def charge := 8628796958913331200

private theorem table : ∀ i j : Fin 19,sideCharge tag (tag root) (i.val,j.val)=weights (i.val,j.val) := by native_decide
private theorem anchor : ∀ i : Sides 12 (tag root),∃ j,(groupSide tag i j).1≠(groupSide tag i j).2 := by native_decide
private theorem bounds : (cycleLists 18 2 18).all (fun cs => decide
    (quickBill 18 weights cs ≤ base+charge*cs.count 2))=true := by native_decide

/-- Exact for any ordinary coloring with an anchor having at most one alternating four-cycle in total.
Cycle sizes in its frame are measured in anchor edges. -/
theorem exact (g : Coloring 36 35) (a : Fin 35) (e : Point 18 ≃ Fin 36)
    (cs : {c : Fin 35 // c≠a} → List Nat) (ord : ∀ c,OrderedCycles 18 2 (cs c))
    (frame : InFrame g a e (fun c => cyclePerm 18 (cs c)))
    (short : (∑ c,(cs c).count 2)≤1) : Exact g 24 := by
  have size : Fintype.card {c : Fin 35 // c≠a}=34 := by simp
  have each c := of_decide_eq_true (List.all_eq_true.mp bounds _ (cycle_member (by decide) (ord c)))
  have total := sum_le_sum (s:=(univ : Finset {c : Fin 35 // c≠a})) (fun c _ => each c)
  simp only [sum_add_distrib,sum_const,card_univ,size,nsmul_eq_mul,←mul_sum] at total
  have budget : (∑ c,quickBill 18 weights (cs c))<(18 : Nat).factorial*2^18 := by
    have price := Nat.mul_le_mul_left charge short
    have limit : 34*base+charge*1 < (18 : Nat).factorial*2^18 := by decide
    omega
  have upper := template_sum g a e cs frame tag root weights table anchor budget
  have sz : starCost tag=24 := by native_decide
  exact exact_of_upper (sz ▸ upper) (fun _ => even_lower (by decide) g)

#print axioms exact
end WildAnchor.K36
