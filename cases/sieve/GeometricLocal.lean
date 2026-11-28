import GeometricBounds
import Mathlib.Algebra.BigOperators.Fin

namespace WildSieve.Geometric
open Finset

private def allPrice (p x s : Nat) :=
  if x≤s ∧ (s-x)%2=0 then p.choose ((s-x)/2) else 0
private def forcedPrice (p x s : Nat) := if x=0 then 0 else allPrice p x s
private def regularPrice (p x s : Nat) :=
  if x≤s ∧ (s-x)%2=0 ∧ 0<(s-x)/2 then p.choose ((s-x)/2-1) else 0

private theorem prices (r : CutRow) (p s N : Nat) (pool : r.pairs≤p) :
    rowAll r s N≤allPrice p r.forced s ∧
    rowSpecial r s N≤forcedPrice p r.forced s ∧
    rowRegular r s N≤regularPrice p r.forced s := by
  have top : min r.pairs ((N-r.forced)/2)≤p := (min_le_left ..).trans pool
  have all : rowAll r s N≤allPrice p r.forced s := by
    unfold rowAll allPrice;split
    · rw [←Nat.choose_eq_fast_choose];exact Nat.choose_le_choose _ top
    · rfl
  refine ⟨all,?_,?_⟩
  · unfold rowSpecial forcedPrice;split <;> first | rfl | exact all
  · unfold rowRegular regularPrice
    dsimp only
    by_cases ok : r.forced≤s ∧ (s-r.forced)%2=0 ∧ 0<(s-r.forced)/2
    · rw [if_pos ok];split
      · rw [←Nat.choose_eq_fast_choose];exact Nat.choose_le_choose _ (by omega)
      · exact Nat.zero_le _
    · rw [if_neg ok,if_neg (by tauto)]

private theorem scalar_caps (n N b d s p : Nat) (hp : N/2≤p) :
    rowCap n N b d s≤d.choose 2*allPrice p (d-2) s+((b-d).choose 2+n)*allPrice p d s ∧
    rowCap n N b d s≤d*max (forcedPrice p (d-2) s) (forcedPrice p d s)+
      (N-1)*max (regularPrice p (d-2) s) (regularPrice p d s) := by
  let r := rowData n N b d
  have pool (i : Fin 3) : (r i).pairs≤p := by
    simp only [r,rowData]
    split
    · dsimp only;omega
    · split <;> dsimp only <;> omega
  have pr (i : Fin 3) := prices (r i) p s N (pool i)
  have atIndex (u : Nat → Nat) (i : Fin 3) : u (r i).forced≤max (u (d-2)) (u d) := by
    simp only [r,rowData]
    split
    · exact le_max_left ..
    · split <;> exact le_max_right ..
  have peakle (v : Fin 3 → Nat) (u : Nat → Nat) (h : ∀ i,v i≤u (r i).forced) :
      peak v≤max (u (d-2)) (u d) := by
    have h' i := (h i).trans (atIndex u i)
    exact max_le (h' 0) (max_le (h' 1) (h' 2))
  constructor
  · apply (min_le_left ..).trans
    change (∑ i,(r i).colors*rowAll (r i) s N) ≤ _
    apply (sum_le_sum fun i _ => Nat.mul_le_mul_left (r i).colors (pr i).1).trans
    simp only [Fin.sum_univ_three,r,rowData]
    simp only [if_pos rfl,if_neg (by decide : (1:Fin 3)≠0),if_neg (by decide : (2:Fin 3)≠0),if_neg (by decide : (2:Fin 3)≠1),if_true]
    nlinarith only [Nat.mul_le_mul_right (allPrice p d s) (Nat.sub_le n (b.choose 2))]
  · apply (min_le_right ..).trans
    exact Nat.add_le_add (Nat.mul_le_mul_left _ (peakle (fun i => rowSpecial (r i) s N) (fun x => forcedPrice p x s) (fun i => (pr i).2.1)))
      (Nat.mul_le_mul_left _ (peakle (fun i => rowRegular (r i) s N) (fun x => regularPrice p x s) (fun i => (pr i).2.2)))

/-- At most one color can force a given vertex as the partner of the
root. A six-set through that vertex needs at most two more matched edges. -/
theorem degree_caps (n f t m : Nat) (size : t=2*m ∨ t=2*m+1)
    (nf : n=3*t+f) (shape : f=0 ∨ f=4 ∨ f=5) (big : 200≤m) :
    degree n f t 1≤10*m ∧ degree n f t 2≤31*m^3 := by
  let N := 3*t
  let p := 3*m+1
  have room : N/2≤p := by dsimp [N,p];omega
  have b (d s : Nat) := scalar_caps n N (f+1) d s p room
  have pk : 2*p.choose 2≤p*p := by
    rw [Nat.choose_two_right,Nat.mul_comm 2]
    exact (Nat.div_mul_le_self ..).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  have p1 : 0<p := by dsimp [p];omega
  have bounded : ∀ a≤6,(a:Nat).choose 2≤15 := by
    intro a ha;exact (Nat.choose_le_choose 2 ha).trans_eq (by decide)
  have small (d) := bounded (f+1-d) (by omega)
  have ord0 := (b 0 3).1
  have ord1 := (b 1 3).2
  have six0 := (b 0 6).2
  have six1 := (b 1 6).1
  have c43 := (b 4 3).1
  have c53 := (b 5 3).1
  have c63 := (b 6 3).1
  have c46 := (b 4 6).1
  have c56 := (b 5 6).1
  have c66 := (b 6 6).1
  norm_num [allPrice,regularPrice,forcedPrice,Nat.choose_one_right,Nat.choose_zero_right] at ord0 ord1 six0 six1 c43 c53 c63 c46 c56 c66
  have s4 := Nat.mul_le_mul_right p (small 4)
  have s6 := small 6
  have safe : degree n f t 1≤N+p+10 ∧
      degree n f t 2≤(N+6)*p.choose 2+(n+30)*p+(n+15) := by
    have h4 : (f+1-4).choose 2*p≤15*p := s4
    have num2 : (4:Nat).choose 2=6 := by decide
    have num5 : (5:Nat).choose 2=10 := by decide
    have num6 : (6:Nat).choose 2=15 := by decide
    simp only [num2,num5,num6,Nat.add_mul] at c46 c53 c66
    unfold degree widths
    have bigT : 4<t := by omega
    have monot := Nat.mul_le_mul_right (p.choose 2) (Nat.sub_le N 1)
    rcases shape with rfl|rfl|rfl <;> simp [bigT,show 2<t by omega] <;>
      simp only [N,Nat.reduceAdd,Nat.reduceSub,Nat.reduceMul,Nat.add_mul] at * <;> constructor <;> omega
  constructor
  · dsimp [N,p] at safe;omega
  · apply safe.2.trans
    have Nle : N≤6*m+3 := by dsimp [N];omega
    have nle : n≤6*m+8 := by omega
    have a := Nat.mul_le_mul_right (p.choose 2) (Nat.add_le_add_right Nle 6)
    have b := Nat.mul_le_mul_right p (Nat.add_le_add_right nle 30)
    have c := Nat.add_le_add_right nle 15
    apply (Nat.add_le_add (Nat.add_le_add a b) c).trans
    have mul := Nat.mul_le_mul_left (6*m+3+6) pk
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le big
    dsimp only [p] at *
    nlinarith only [mul,Nat.zero_le k,Nat.zero_le (k*k),Nat.zero_le (k*k*k)]

end WildSieve.Geometric
