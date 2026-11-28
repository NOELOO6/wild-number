import GeometricLocal
import GeometricTail

namespace WildSieve.Geometric
open Finset WildExact

private theorem consecutive (k : Nat) :
    (ways (k+1):ℚ)*2=(ways k:ℚ)*(3*k+2)*(3*k+1) := by
  have e := Nat.choose_succ_right_eq (3*k+2) 1
  simp only [Nat.choose_one_right,show 3*k+2-1=3*k+1 by omega] at e
  rw [ways,←Nat.choose_eq_fast_choose,Nat.cast_mul]
  have c : (((3*k+2).choose 2:Nat):ℚ)*2=(3*k+2)*(3*k+1) := by exact_mod_cast e
  have v := congrArg (fun q : ℚ => q*(ways k:ℚ)) c
  dsimp only at v
  linarith only [v]

private theorem short_weights (t : Nat) (two : 2≤t) :
    sealWeight t 1*(3*t-1)*(3*t-2)=2 ∧
    sealWeight t 2*(3*t-1)*(3*t-2)*(3*t-4)*(3*t-5)=40 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le two
  have a := consecutive (k+1)
  have b := consecutive k
  have den : (ways (2+k):ℚ)≠0 := by exact_mod_cast (ways_pos _).ne'
  rw [show k+1+1=2+k by omega] at a
  unfold sealWeight
  rw [show 2+k-1=k+1 by omega,show 2+k-2=k by omega,show ways 1=1 by decide,show ways 2=10 by decide]
  push_cast at a b ⊢
  constructor
  · field_simp [den]
    linarith only [a]
  · field_simp [den]
    have both := congrArg (fun x : ℚ => x*(3*(k+1)+2)*(3*(k+1)+1)) b
    dsimp only at both
    linarith only [a,both]

theorem local_enough (n f t m : Nat) (size : t=2*m ∨ t=2*m+1) (nf : n=3*t+f)
    (shape : f=0 ∨ f=4 ∨ f=5) (big : 200≤m) :
    (degree n f t 1:ℚ)*sealWeight t 1*(rate m)^3+
      (degree n f t 2:ℚ)*sealWeight t 2*(rate m)^6≤rate m-1 := by
  have mr : (200:ℚ)≤m := by exact_mod_cast big
  have mp : (0:ℚ)<m := by linarith
  have tr : 2*(m:ℚ)≤t := by exact_mod_cast (show 2*m≤t by omega)
  have num := degree_caps n f t m size nf shape big
  have a : (degree n f t 1:ℚ)≤10*m := by exact_mod_cast num.1
  have b : (degree n f t 2:ℚ)≤31*(m:ℚ)^3 := by exact_mod_cast num.2
  let p : ℚ := (59/10)*m
  have pp : 0<p := by dsimp [p];positivity
  have f1 : p≤3*t-1 := by dsimp [p];linarith
  have f2 : p≤3*t-2 := by dsimp [p];linarith
  have f4 : p≤3*t-4 := by dsimp [p];linarith
  have f5 : p≤3*t-5 := by dsimp [p];linarith
  have wpos (j) : 0≤sealWeight t j := div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  obtain ⟨w1,w2⟩ := short_weights t (by omega)
  have pair := mul_le_mul f1 f2 pp.le (pp.le.trans f1)
  have four := mul_le_mul (mul_le_mul pair f4 pp.le (mul_nonneg (pp.le.trans f1) (pp.le.trans f2))) f5 pp.le
    (mul_nonneg (mul_nonneg (pp.le.trans f1) (pp.le.trans f2)) (pp.le.trans f4))
  have q1 : sealWeight t 1*p^2≤2 := by
    have h := mul_le_mul_of_nonneg_left pair (wpos 1)
    linarith only [h,w1]
  have q2 : sealWeight t 2*p^4≤40 := by
    have h := mul_le_mul_of_nonneg_left four (wpos 2)
    linarith only [h,w2]
  have r := rate_limits m big
  have lim (j : Nat) (hj : j≤6) : (rate m)^j≤11/10 := calc
    (rate m)^j ≤ (rate m)^6 := pow_le_pow_right₀ r.1 hj
    _ ≤ (101/100:ℚ)^6 := pow_le_pow_left₀ (le_trans (by decide) r.1) r.2.1 _
    _ ≤ _ := by norm_num
  have calc1 := mul_le_mul (mul_le_mul a ((le_div_iff₀ (pow_pos pp 2)).mpr q1) (wpos 1) (by positivity))
    (lim 3 (by decide)) (pow_nonneg (le_trans (by decide) r.1) _)
    (mul_nonneg (by positivity) (div_nonneg (by norm_num) (pow_nonneg pp.le _)))
  have calc2 := mul_le_mul (mul_le_mul b ((le_div_iff₀ (pow_pos pp 4)).mpr q2) (wpos 2) (by positivity))
    (lim 6 (by decide)) (pow_nonneg (le_trans (by decide) r.1) _)
    (mul_nonneg (by positivity) (div_nonneg (by norm_num) (pow_nonneg pp.le _)))
  apply (add_le_add calc1 calc2).trans
  have eq : 10*(m:ℚ)*(2/p^2)*(11/10)+31*(m:ℚ)^3*(40/p^4)*(11/10)=
      (10*(2/(59/10)^2)*(11/10)+31*(40/(59/10)^4)*(11/10))/(m:ℚ) := by
    dsimp only [p]
    field_simp [mp.ne']; ring
  rw [eq,rate,add_sub_cancel_left]
  exact div_le_div_of_nonneg_right (by norm_num) mp.le

/-- Above the finite comparison range the same geometric certificate
works at every order, in all three residue classes. -/
theorem large (n : Nat) (lo : 1207≤n) (odd : n%2=1) :
    (∀ g : Coloring n n,Exact g ((2*n+2)/3)) ∧ (∀ g : Coloring (n+1) n,Exact g ((2*n+2)/3)) := by
  let f := fixedSize n
  let t := levels n
  let m := t/2
  have shape : f=0 ∨ f=4 ∨ f=5 := by
    dsimp [f,fixedSize]
    split
    · exact Or.inl rfl
    · split <;> simp
  have nf : n=3*t+f := by
    by_cases h : n%3=0
    · simp only [t,f,levels,fixedSize,if_pos h];omega
    by_cases h1 : n%3=1 <;> simp [t,f,levels,fixedSize,h,h1] <;> omega
  have sz : t=2*m ∨ t=2*m+1 := by dsimp [m];omega
  have big : 200≤m := by omega
  have c := cert n f t _ (rate_limits m big).1 (local_enough n f t m sz nf shape big)
    (long_enough n f t m sz nf shape big)
  apply exact_from_rule n (by omega) odd
  intro F B r hr bs ws rain
  exact frozen_layout F B r _ _ hr bs ws rain _ (by simpa only [Fintype.card_fin] using c)

#print axioms large
end WildSieve.Geometric
