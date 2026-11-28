import GeometricBounds
import EvenRatios
import Mathlib.Algebra.BigOperators.Fin

namespace WildSieve.Geometric
open Finset EvenTriples

private theorem choose_up {n a b : Nat} (le : a≤b) (half : b≤n/2) : n.choose a≤n.choose b := by
  induction b with
  | zero => simp [show a=0 by omega]
  | succ b ih =>
    by_cases e : a=b+1
    · rw [e]
    · exact (ih (by omega) (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

private theorem row_envelope (r : CutRow) (m s : Nat) (pp : r.pairs≤3*m+1) (half : s≤3*m) (u : Nat) :
    rowAll r s u≤2*(3*m).choose (s/2) := by
  unfold rowAll
  split
  · simp only [←Nat.choose_eq_fast_choose]
    apply (Nat.choose_le_choose _ ((min_le_left ..).trans pp)).trans
    apply (choose_up (by omega : (s-r.forced)/2≤s/2) (by omega : s/2≤(3*m+1)/2)).trans
    cases h : s/2 with
    | zero => simp
    | succ k =>
      rw [Nat.choose_succ_succ]
      have := choose_up (by omega : k≤k+1) (by omega : k+1≤(3*m)/2)
      simpa only [Nat.succ_eq_add_one] using (show (3*m).choose k+(3*m).choose (k+1)≤2*(3*m).choose (k+1) by omega)
  · exact Nat.zero_le _

private theorem total_envelope (n N b d s m : Nat) (nn : n≤6*m+8) (size : N≤6*m+3)
    (small : b≤6) (db : d≤b) (half : s≤3*m) (big : 200≤m) :
    totalFor n N b d s N≤4*(6*m-1)*(3*m).choose (s/2) := by
  let r := rowData n N b d
  have pool (i : Fin 3) : (r i).pairs≤3*m+1 := by
    simp only [r,rowData];split
    · dsimp only;omega
    · split <;> dsimp only <;> omega
  have single (i : Fin 3) := Nat.mul_le_mul_left (r i).colors (row_envelope (r i) m s (pool i) half N)
  have sum := sum_le_sum (s:=univ) (fun i _ => single i)
  simp only [←sum_mul] at sum
  have cols : (∑ i,(r i).colors)≤2*(6*m-1) := by
    have a := Nat.choose_le_choose 2 (db.trans small)
    have b' := Nat.choose_le_choose 2 (show b-d≤6 by omega)
    simp only [Fin.sum_univ_three,r,rowData,if_pos,if_false,Fin.reduceFinMk,Fin.isValue,Fin.reduceEq]
    have six : (6:Nat).choose 2=15 := by decide
    rw [six] at a b'
    norm_num
    omega
  apply sum.trans
  calc
    _ ≤ (2*(6*m-1))*(2*(3*m).choose (s/2)) := Nat.mul_le_mul_right _ cols
    _ = _ := by ring

theorem count_envelope (n f t m j : Nat) (size : t=2*m ∨ t=2*m+1)
    (nf : n=3*t+f) (shape : f=0 ∨ f=4 ∨ f=5) (half : 2*j≤t) (big : 200≤m) :
    countBound n f t j≤16*(6*m-1)*(3*m).choose (3*j/2) := by
  let q := 4*(6*m-1)*(3*m).choose (3*j/2)
  have each (d : Nat) (hd : d≤f+1) : totalFor n (3*t) (f+1) d (3*j) (3*t)≤q :=
    total_envelope _ _ _ _ _ _ (by omega) (by omega) (by omega) hd (by omega) big
  have h0 := each 0 (by omega)
  have h1 := each 1 (by omega)
  have h2 := each f (by omega)
  have h3 := each (f+1) (by omega)
  have eq : 16*(6*m-1)*(3*m).choose (3*j/2)=4*q := by dsimp [q];ring
  rw [eq];unfold countBound widths
  split <;> simp only [List.append_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero] <;> omega

private theorem one_more (t j : Nat) (inside : j≤t) : sealWeight (t+1) j≤sealWeight t j := by
  have p : 0<(ways t:ℚ) := by exact_mod_cast ways_pos _
  have q : 0<(ways (t+1):ℚ) := by exact_mod_cast ways_pos _
  unfold sealWeight
  apply (div_le_div_iff₀ q p).mpr
  rw [show t+1-j=(t-j)+1 by omega]
  have ch := Nat.choose_le_choose 2 (show 3*(t-j)+2≤3*t+2 by omega)
  simp only [ways,←Nat.choose_eq_fast_choose,Nat.cast_mul]
  have scaled := mul_le_mul_of_nonneg_left (show (((3*(t-j)+2).choose 2:Nat):ℚ)≤(3*t+2).choose 2 by exact_mod_cast ch)
    (show (0:ℚ)≤(ways j:ℚ)*ways (t-j)*ways t by positivity)
  linarith only [scaled]

private theorem two_step (j : Nat) : ways (2*j+1)=(3*j+1)*(6*j+1)*ways (2*j) := by
  have e : (3*(2*j)+2).choose 2=(3*j+1)*(6*j+1) := by
    rw [Nat.choose_two_right,show 3*(2*j)+2-1=6*j+1 by omega,
      show (3*(2*j)+2)*(6*j+1)=((3*j+1)*(6*j+1))*2 by ring,Nat.mul_div_cancel _ (by decide : 0<2)]
  rw [ways,←Nat.choose_eq_fast_choose,e]

private theorem even_step (j : Nat) : ways (2*(j+1))=(3*j+2)*(6*j+5)*ways (2*j+1) := by
  have e : (3*(2*j+1)+2).choose 2=(3*j+2)*(6*j+5) := by
    rw [Nat.choose_two_right,show 3*(2*j+1)+2-1=6*j+4 by omega,
      show (3*(2*j+1)+2)*(6*j+4)=((3*j+2)*(6*j+5))*2 by ring,Nat.mul_div_cancel _ (by decide : 0<2)]
  rw [show 2*(j+1)=(2*j+1)+1 by omega,ways,←Nat.choose_eq_fast_choose,e]

private theorem odd_vs_even (r k : Nat) :
    let m := r+k+1
    ((6*m-1:Nat):ℚ)*((3*m).choose (3*r+1):ℚ)*sealWeight (2*m) (2*r+1) ≤ 2*mass m (r+1) := by
  dsimp only
  let m := r+k+1
  let n := 3*m
  have a := Nat.choose_succ_right_eq n (3*r+1)
  have b := Nat.choose_succ_right_eq n (3*r+2)
  rw [show n-(3*r+1)=3*k+2 by dsimp [n,m];omega] at a
  rw [show n-(3*r+2)=3*k+1 by dsimp [n,m];omega] at b
  have ch : ((n.choose (3*r+1):ℕ):ℚ)*(3*k+2)*(3*k+1)=
      (n.choose (3*(r+1)):ℚ)*(3*r+3)*(3*r+2) := by
    exact_mod_cast (show n.choose (3*r+1)*(3*k+2)*(3*k+1)=n.choose (3*(r+1))*(3*r+3)*(3*r+2) by
      rw [←a,show 3*(r+1)=3*r+2+1 by omega];nlinarith only [congrArg (·*(3*r+2)) b])
  have rel : (n.choose (3*r+1):ℚ)*(3*k+1)*(6*k+1) ≤
      2*(n.choose (3*(r+1)):ℚ)*(3*r+2)*(6*r+5) := by
    apply le_of_mul_le_mul_right (a:=3*(k:ℚ)+2) _ (by positivity)
    have q := congrArg (·*(6*(k:ℚ)+1)) ch
    have c : (3*(r:ℚ)+3)*(6*k+1)≤2*(6*r+5)*(3*k+2) := by nlinarith only [Nat.cast_nonneg (α:=ℚ) r,Nat.cast_nonneg (α:=ℚ) k,mul_nonneg (Nat.cast_nonneg (α:=ℚ) r) (Nat.cast_nonneg (α:=ℚ) k)]
    have scaled := mul_le_mul_of_nonneg_left c (show 0≤(n.choose (3*(r+1)):ℚ)*(3*r+2) by positivity)
    dsimp only at q
    linarith only [q,scaled]
  unfold sealWeight mass
  change ((6*m-1:Nat):ℚ)*((3*m).choose (3*r+1):ℚ)*(_ / _) ≤ 2*(((6*m-1:Nat):ℚ)*((3*m).choose (3*(r+1)):ℚ)*_ * _ / _)
  rw [show 2*m-(2*r+1)=2*k+1 by dsimp [m];omega,show m-(r+1)=k by dsimp [m];omega,
    two_step k,even_step r]
  push_cast
  have w : 0≤((6*m-1:Nat):ℚ)*ways (2*r+1)*ways (2*k)/(ways (2*m):ℚ) :=
    div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have paid := mul_le_mul_of_nonneg_left rel w
  dsimp [n] at paid
  simpa only [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using paid

theorem mass_envelope (n f t m j : Nat) (size : t=2*m ∨ t=2*m+1)
    (nf : n=3*t+f) (shape : f=0 ∨ f=4 ∨ f=5) (half : 2*j≤t) (big : 200≤m) :
    (countBound n f t j:ℚ)*sealWeight t j≤32*mass m ((j+1)/2) := by
  have c := count_envelope n f t m j size nf shape half big
  have hs : sealWeight t j≤sealWeight (2*m) j := by
    rcases size with rfl|rfl
    · rfl
    · exact one_more _ _ (by omega)
  have hp : 0≤sealWeight t j := div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have cap := mul_le_mul (show (countBound n f t j:ℚ)≤(16:ℚ)*(6*m-1:Nat)*((3*m).choose (3*j/2):ℚ) by exact_mod_cast c) hs hp (by positivity)
  apply cap.trans
  rcases Nat.mod_two_eq_zero_or_one j with even|odd
  · let r := j/2
    have h : j=2*r := by dsimp [r];omega
    rw [show (j+1)/2=r by dsimp [r];omega,show 3*j/2=3*r by omega,h]
    have eq : ((6*m-1:Nat):ℚ)*((3*m).choose (3*r):ℚ)*sealWeight (2*m) (2*r)=mass m r := by
      unfold mass sealWeight
      rw [show 2*m-2*r=2*(m-r) by omega];ring
    linarith only [eq,mass_nonneg m r]
  · let r := j/2
    let k := m-r-1
    have hr : j=2*r+1 := by dsimp [r];omega
    have mEq : r+k+1=m := by dsimp [k];omega
    have e := odd_vs_even r k
    dsimp only at e
    rw [mEq] at e
    rw [show (j+1)/2=r+1 by omega,show 3*j/2=3*r+1 by omega,hr]
    linarith only [e]

end WildSieve.Geometric
