import GeometricMass
import Mathlib.Algebra.Order.Ring.Pow

namespace WildSieve.Geometric
open Finset EvenTriples

theorem rate_limits (m : Nat) (big : 200≤m) :
    1≤rate m ∧ rate m≤101/100 ∧ ∀ j≤m,(rate m)^(3*j)≤32768 := by
  have hm : (200:ℚ)≤m := by exact_mod_cast big
  have pos : (0:ℚ)<m := by linarith
  have one : 1≤rate m := by unfold rate; linarith only [div_nonneg (by decide : (0:ℚ)≤2) pos.le]
  have cap : 2/(m:ℚ)≤1/100 := (div_le_iff₀ pos).mpr (by linarith)
  refine ⟨one,by unfold rate;linarith,?_⟩
  let q := m/4
  have four : (4:ℚ)*q≤m := by exact_mod_cast (show 4*q≤m by dsimp [q];omega)
  let x : ℚ := 2/(m+2)
  have den : (0:ℚ)<m+2 := by linarith
  have xsmall : x≤1 := (div_le_iff₀ den).mpr (by linarith)
  have xnon : 0≤x := div_nonneg (by decide) den.le
  have prod : (1-x)*rate m=1 := by unfold x rate;field_simp
  have qx : (q:ℚ)*x≤1/2 := by dsimp [x];rw [←mul_div_assoc];apply (div_le_iff₀ den).mpr;linarith
  have ber := one_add_mul_le_pow (a:= -x) (by linarith : -2≤ -x) q
  have half : (1/2:ℚ)≤(1-x)^q := by simpa only [sub_eq_add_neg] using (show (1/2:ℚ)≤(1+ -x)^q by linarith only [ber,qx])
  have mult := mul_le_mul_of_nonneg_right half (pow_nonneg (by linarith only [one] : 0≤rate m) q)
  rw [←mul_pow,prod,one_pow] at mult
  have qb : (rate m)^q≤2 := by linarith
  intro j hj
  have exp : 3*j≤q*15 := by dsimp [q];omega
  calc
    _ ≤ (rate m)^(q*15) := pow_le_pow_right₀ one exp
    _ = ((rate m)^q)^15 := pow_mul ..
    _ ≤ (2:ℚ)^15 := pow_le_pow_left₀ (pow_nonneg (by linarith only [one]) _) qb _
    _ = _ := by norm_num

private def coefficient (j : Nat) : ℚ := if j=1 then 7/6 else j+1

private theorem ratio_small (m j : Nat) (big : 200≤m) (lo : 1≤j) (hi : j≤5) :
    mass m (j+1)*(m:ℚ)≤coefficient j*mass m j := by
  let k := m-j-1
  have eq : j+k+1=m := by dsimp [k];omega
  have kh : (190:ℚ)≤k := by exact_mod_cast (show 190≤k by dsimp [k];omega)
  have poly : ((k:ℚ)+1)*(6*j+1)*(6*j+5)*(j+k+1)≤coefficient j*((j:ℚ)+1)*(6*k+1)*(6*k+5) := by
    have o : j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
    rcases o with rfl|rfl|rfl|rfl|rfl <;> norm_num [coefficient] <;>
      nlinarith only [sq_nonneg ((k:ℚ)-190),kh]
  have mr : (m:ℚ)=j+k+1 := by exact_mod_cast eq.symm
  rw [←mr] at poly
  have step := mass_step j k
  rw [eq] at step
  have lhs := congrArg (fun q : ℚ => q*m) step
  dsimp only at lhs
  have upper := mul_le_mul_of_nonneg_left poly (mass_nonneg m j)
  apply le_of_mul_le_mul_right (a:=((j:ℚ)+1)*(6*k+1)*(6*k+5)) _ (by positivity)
  linarith only [lhs,upper]

private theorem scaled (m : Nat) (big : 200≤m) :
    mass m 2*m≤1 ∧ mass m 3*(m:ℚ)^2≤3 ∧ mass m 6*(m:ℚ)^5≤360 := by
  have mr : (200:ℚ)≤m := by exact_mod_cast big
  have first := first_mass m (by omega)
  have b1 : mass m 1≤6/7 := by
    apply le_of_mul_le_mul_right (a:=6*(m:ℚ)-5) _ (by linarith)
    rw [first]
    linarith
  have t := ratio_small m 1 big (by decide) (by decide)
  norm_num [coefficient] at t
  have b2 : mass m 2*m≤1 := by linarith only [t,b1]
  have lift (j h : Nat) (lo : 2≤j) (hi : j≤5) (A : ℚ) (bound : mass m j*(m:ℚ)^h≤A) :
      mass m (j+1)*(m:ℚ)^(h+1)≤((j:ℚ)+1)*A := by
    have st := ratio_small m j big (by omega) hi
    rw [coefficient,if_neg (by omega)] at st
    have u := mul_le_mul_of_nonneg_right st (pow_nonneg (Nat.cast_nonneg (α:=ℚ) m) h)
    have v := mul_le_mul_of_nonneg_left bound (show (0:ℚ)≤j+1 by positivity)
    rw [pow_succ]
    linarith only [u,v]
  have b3 := lift 2 1 (by decide) (by decide) 1 (by simpa using b2)
  norm_num at b3
  have b4 := lift 3 2 (by decide) (by decide) 3 b3
  norm_num at b4
  have b5 := lift 4 3 (by decide) (by decide) 12 b4
  norm_num at b5
  have b6 := lift 5 4 (by decide) (by decide) 60 b5
  norm_num at b6
  exact ⟨b2,b3,b6⟩

private theorem symmetric (m i : Nat) (le : i≤m) : mass m (m-i)=mass m i := by
  unfold mass
  rw [show 3*(m-i)=3*m-3*i by omega,Nat.choose_symm (by omega),show m-(m-i)=i by omega]
  ring

private theorem later (m i r : Nat) (low : r≤i) (near : 2*i≤m+1) (room : 2*r≤m) :
    mass m i≤mass m r := by
  by_cases h : 2*i≤m
  · exact decreasing m r i low h
  · rw [←symmetric m i (by omega)]
    exact decreasing m r _ (by omega) (by omega)

private theorem fixed_scale (m h : Nat) (big : 200≤m) (p A : ℚ) (pos : 0≤p) (bound : p*(m:ℚ)^h≤A) :
    p≤A/(200:ℚ)^h := by
  apply (le_div_iff₀ (by positivity)).mpr
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) (by exact_mod_cast big : (200:ℚ)≤m) h) pos).trans bound

theorem long_enough (n f t m : Nat) (size : t=2*m ∨ t=2*m+1) (nf : n=3*t+f)
    (shape : f=0 ∨ f=4 ∨ f=5) (big : 200≤m) :
    (∑ j∈longLevels t,(countBound n f t j:ℚ)*sealWeight t j*(rate m)^(3*j))<1 := by
  let S := longLevels t
  let far := 32*32768*mass m 6
  have loc := rate_limits m big
  have bounds := scaled m big
  have a := fixed_scale m 1 big _ 1 (mass_nonneg m 2) (by simpa using bounds.1)
  have b := fixed_scale m 2 big _ 3 (mass_nonneg m 3) bounds.2.1
  have c := fixed_scale m 4 big (m*mass m 6) 360 (mul_nonneg (Nat.cast_nonneg _) (mass_nonneg ..)) (by
    calc (m*mass m 6)*(m:ℚ)^4=mass m 6*(m:ℚ)^5 := by ring
         _ ≤ _ := bounds.2.2)
  have farpos : 0≤far := mul_nonneg (by norm_num) (mass_nonneg ..)
  have step (j : Nat) (hj : j∈S) : (countBound n f t j:ℚ)*sealWeight t j*(rate m)^(3*j)≤
      (if j≤4 then (64:ℚ)/200 else 0)+(if j≤10 then (64:ℚ)*3/200^2 else 0)+far := by
    obtain ⟨inRange,lower⟩ := mem_filter.mp hj
    have hi := mem_range.mp inRange
    have half : 2*j≤t := by omega
    have mk := mass_envelope n f t m j size nf shape half big
    let i := (j+1)/2
    have room : 2*i≤m+1 := by dsimp [i];omega
    have weight : 0≤(rate m)^(3*j) := pow_nonneg (by linarith only [loc.1]) _
    by_cases h : j≤10
    · have boost : (rate m)^(3*j)≤2 := calc
        _ ≤ (rate m)^30 := pow_le_pow_right₀ loc.1 (by omega)
        _ ≤ (101/100:ℚ)^30 := pow_le_pow_left₀ (by linarith only [loc.1]) loc.2.1 _
        _ ≤ _ := by norm_num
      have z := mul_le_mul mk boost weight (mul_nonneg (by norm_num) (mass_nonneg ..))
      rw [if_pos h]
      by_cases small : j≤4
      · rw [if_pos small]
        have mi := later m i 2 (by dsimp [i];omega) room (by omega)
        change _≤32*mass m i*2 at z
        linarith only [z,mi,a,farpos]
      · rw [if_neg small]
        have mi := later m i 3 (by dsimp [i];omega) room (by omega)
        change _≤32*mass m i*2 at z
        linarith only [z,mi,b,farpos]
    · rw [if_neg h,if_neg (by omega : ¬j≤4),zero_add,zero_add]
      have boost := loc.2.2 j (by omega)
      have mi := later m i 6 (by dsimp [i];omega) room (by omega)
      have z := mul_le_mul mk boost weight (mul_nonneg (by norm_num) (mass_nonneg ..))
      dsimp only [far]
      change _≤32*mass m i*32768 at z
      linarith only [z,mi]
  have number (v : Nat) (h : 3≤v) : (S.filter (·≤v)).card≤v-2 := by
    have sub : S.filter (·≤v)⊆Icc 3 v := fun j hj => mem_Icc.mpr ⟨(mem_filter.mp (mem_filter.mp hj).1).2,(mem_filter.mp hj).2⟩
    exact (card_le_card sub).trans_eq (by rw [Nat.card_Icc];omega)
  have total := sum_le_sum step
  rw [sum_add_distrib,sum_add_distrib,←sum_filter,←sum_filter,sum_const,sum_const,sum_const] at total
  simp only [nsmul_eq_mul] at total
  have s4 : ((S.filter (·≤4)).card:ℚ)≤2 := by exact_mod_cast number 4 (by decide)
  have s10 : ((S.filter (·≤10)).card:ℚ)≤8 := by exact_mod_cast number 10 (by decide)
  have len : (S.card:ℚ)≤(m:ℚ)+1 := by
    exact_mod_cast (card_le_card (filter_subset _ _)).trans (show (range (t/2+1)).card≤m+1 by rw [card_range];omega)
  have mr : (200:ℚ)≤m := by exact_mod_cast big
  have v := mul_le_mul_of_nonneg_right len farpos
  have e := mul_le_mul_of_nonneg_right (show (m:ℚ)+1≤(201/200)*m by linarith) farpos
  dsimp only [far] at v e total
  linarith only [total,s4,s10,v,e,c]

end WildSieve.Geometric
