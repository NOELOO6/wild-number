import EvenRatios
namespace WildSieve.EvenTriples
open Finset

private theorem initial_bounds (m : Nat) (big : 70≤m) :
    mass m 1≤6/7 ∧ mass m 2*m≤2*mass m 1 ∧ mass m 3*m≤4*mass m 2 := by
  have m1 := first_mass m (by omega)
  have mr : (70:ℚ)≤m := by exact_mod_cast big
  have a : mass m 1≤6/7 := by
    apply le_of_mul_le_mul_right (a:=(6*(m:ℚ)-5)) _ (by linarith)
    rw [m1]
    linarith
  obtain ⟨h,eq⟩ := Nat.exists_eq_add_of_le big
  let k := m-2
  let l := m-3
  have ek : 1+k+1=m := by dsimp [k]; omega
  have el : 2+l+1=m := by dsimp [l]; omega
  have m2 := mass_step 1 k
  have m3 := mass_step 2 l
  rw [ek] at m2
  rw [el] at m3
  have rk : (k:ℚ)=(h:ℚ)+68 := by exact_mod_cast (show k=h+68 by dsimp [k]; omega)
  have rl : (l:ℚ)=(h:ℚ)+67 := by exact_mod_cast (show l=h+67 by dsimp [l]; omega)
  have rm : (m:ℚ)=(h:ℚ)+70 := by exact_mod_cast (show m=h+70 by omega)
  have poly2 : (k+1:ℚ)*(6*1+1)*(6*1+5)*m ≤ 2*(1+1)*(6*k+1)*(6*k+5) := by
    rw [rk,rm]
    nlinarith only [sq_nonneg (h:ℚ),Nat.cast_nonneg (α:=ℚ) h]
  have poly3 : (l+1:ℚ)*(6*2+1)*(6*2+5)*m ≤ 4*(2+1)*(6*l+1)*(6*l+5) := by
    rw [rl,rm]
    nlinarith only [sq_nonneg (h:ℚ),Nat.cast_nonneg (α:=ℚ) h]
  have p2 := mul_le_mul_of_nonneg_left poly2 (mass_nonneg m 1)
  have p3 := mul_le_mul_of_nonneg_left poly3 (mass_nonneg m 2)
  refine ⟨a,?_,?_⟩
  · apply le_of_mul_le_mul_right (a:=(1+1)*(6*(k:ℚ)+1)*(6*k+5)) _ (by positivity)
    norm_num at m2
    have h2 := congrArg (fun q : ℚ => q*m) m2
    dsimp only at h2
    norm_num at p2 ⊢
    linarith only [h2,p2]
  · apply le_of_mul_le_mul_right (a:=(2+1)*(6*(l:ℚ)+1)*(6*l+5)) _ (by positivity)
    norm_num at m3
    have h3 := congrArg (fun q : ℚ => q*m) m3
    dsimp only at h3
    norm_num at p3 ⊢
    linarith only [h3,p3]

/-- All large multiples of six satisfy the ordinary union bound. -/
theorem large_sum (m : Nat) (big : 70≤m) :
    (∑ j∈shortLevels∪longLevels (2*m),(pureTotal (6*m) (2*m) j:ℚ)*sealWeight (2*m) j)<1 := by
  have mr : (70:ℚ)≤m := by exact_mod_cast big
  have pos : (0:ℚ)<m := by linarith
  let S := shortLevels∪longLevels (2*m)
  let f (j : Nat) : ℚ := (pureTotal (6*m) (2*m) j:ℚ)*sealWeight (2*m) j
  have upper (j : Nat) (even : j%2=0) (le : j≤m) : f j≤mass m (j/2) := by
    let k := j/2
    have eq : j=2*k := by dsimp [k]; omega
    have sub : 2*m-j=2*(m-k) := by omega
    have mul : 3*j=2*(3*k) := by omega
    have sz : (6*m)/2=3*m := by omega
    have cmp : pureTotal (6*m) (2*m) j≤(6*m-1)*(3*m).choose (3*k) := by
      simp only [pureTotal,mul,Nat.mul_mod_right,Nat.zero_mod,if_pos,sz]
      rw [show 2*(3*k)/2=3*k by omega]
      exact Nat.mul_le_mul_left _ (Nat.choose_le_choose _ (Nat.sub_le _ _))
    have wpos : 0≤sealWeight (2*m) j := div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    have q := mul_le_mul_of_nonneg_right (show (pureTotal (6*m) (2*m) j:ℚ)≤((6*m-1:Nat):ℚ)*((3*m).choose (3*k):ℚ) by exact_mod_cast cmp) wpos
    apply q.trans_eq
    unfold sealWeight mass
    change _ = ((6*m-1:Nat):ℚ)*((3*m).choose (3*k):ℚ)*ways (2*k)*ways (2*(m-k))/(ways (2*m):ℚ)
    rw [sub,eq]
    ring
  have range (j) (hj : j∈S) : 1≤j ∧ j≤m := by
    rcases mem_union.mp hj with h|h
    · simp [shortLevels] at h
      omega
    · obtain ⟨h1,h2⟩ := mem_filter.mp h
      have := mem_range.mp h1
      omega
  let R := (S.erase 2).erase 4
  have small (j) (hj : j∈R) : f j≤mass m 3 := by
    obtain ⟨n4,h'⟩ := mem_erase.mp hj
    obtain ⟨n2,h''⟩ := mem_erase.mp h'
    have num := range j h''
    by_cases e : j%2=0
    · exact (upper j e num.2).trans (decreasing m 3 (j/2) (by omega) (by omega))
    · have z : pureTotal (6*m) (2*m) j=0 := by simp [pureTotal,show (3*j)%2≠0 by omega]
      simpa [f,z] using mass_nonneg m 3
  have rcard : R.card≤m+1 := by
    have sub : R⊆Finset.range (m+1) := fun j hj => mem_range.mpr (by
      have h := range j (mem_erase.mp (mem_erase.mp hj).2).2; omega)
    simpa using card_le_card sub
  have two : 2∈S := mem_union_left _ (by decide)
  have four : 4∈S.erase 2 := mem_erase.mpr ⟨by decide,mem_union_right _ (mem_filter.mpr ⟨mem_range.mpr (by omega),by decide⟩)⟩
  have e1 := sum_erase_add (s:=S) f two
  have e2 := sum_erase_add (s:=S.erase 2) f four
  have total := sum_le_sum small
  rw [sum_const,nsmul_eq_mul] at total
  have b := mul_le_mul_of_nonneg_right (show (R.card:ℚ)≤m+1 by exact_mod_cast rcard) (mass_nonneg m 3)
  have f2 := upper 2 (by decide) (by omega)
  have f4 := upper 4 (by decide) (by omega)
  have h := initial_bounds m big
  have b2 : mass m 2≤2*mass m 1/m := (le_div_iff₀ pos).mpr h.2.1
  have b3 : mass m 3≤4*mass m 2/m := (le_div_iff₀ pos).mpr h.2.2
  have d2 : mass m 2≤(2*(6/7))/m := b2.trans (div_le_div_of_nonneg_right (by linarith [h.1]) pos.le)
  have d3 : mass m 3≤(4*((2*(6/7))/m))/m := b3.trans (div_le_div_of_nonneg_right (by linarith only [d2]) pos.le)
  have mind := mul_le_mul_of_nonneg_left d3 (show (0:ℚ)≤m+1 by positivity)
  have rest : (6/7:ℚ)+(2*(6/7))/m+(m+1)*((4*((2*(6/7))/m))/m)<1 := by
    apply lt_of_mul_lt_mul_right (a := (m:ℚ)^2)
    · have clear : ((6/7:ℚ)+(2*(6/7))/m+(m+1)*((4*((2*(6/7))/m))/m)) * (m:ℚ)^2 =
          (6*(m:ℚ)^2+12*m+48*(m+1))/7 := by field_simp [pos.ne']; ring
      rw [clear]
      nlinarith only [sq_nonneg ((m:ℚ)-70),mr]
    · positivity
  change (∑ j∈S,f j)<1
  change (∑ j∈R,f j)+f 4=∑ j∈S.erase 2,f j at e2
  change _≤mass m 1 at f2
  change _≤mass m 2 at f4
  linarith only [total,b,e1,e2,f2,f4,h.1,d2,mind,rest]
end WildSieve.EvenTriples
