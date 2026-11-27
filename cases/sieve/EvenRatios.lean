import EvenOrders
import Mathlib.Tactic.Ring
namespace WildSieve.EvenTriples
open Finset

/-- Contribution of all cuts consisting of 2j triples before orienting
equal sides. The order of the complete graph is 6m. -/
def mass (m j : Nat) : ℚ :=
  ((6*m-1:Nat):ℚ)*((3*m).choose (3*j):ℚ)*ways (2*j)*ways (2*(m-j))/(ways (2*m):ℚ)

private theorem two_ways (j : Nat) :
    ways (2*(j+1))=(6*j+5)*(6*j+1)*(3*j+2)*(3*j+1)*ways (2*j) := by
  have ch (a : Nat) : (2*a+1).choose 2=(2*a+1)*a := by
    rw [Nat.choose_two_right,show 2*a+1-1=2*a by omega]
    rw [show (2*a+1)*(2*a)=((2*a+1)*a)*2 by ring,Nat.mul_div_cancel _ (by decide : 0<2)]
  have ce (a : Nat) : (2*a+2).choose 2=(a+1)*(2*a+1) := by
    rw [Nat.choose_two_right,show 2*a+2-1=2*a+1 by omega]
    rw [show (2*a+2)*(2*a+1)=(a+1)*(2*a+1)*2 by ring,Nat.mul_div_cancel _ (by decide : 0<2)]
  rw [show 2*(j+1)=(2*j+1)+1 by omega]
  simp only [ways,←Nat.choose_eq_fast_choose]
  rw [show 3*(2*j+1)+2=2*(3*j+2)+1 by omega,ch,show 3*(2*j)+2=2*(3*j)+2 by omega,ce]
  ring

private theorem three_choose (j k : Nat) :
    (3*(j+k+1)).choose (3*(j+1))*(j+1)*(3*j+2)*(3*j+1)=
    (3*(j+k+1)).choose (3*j)*(k+1)*(3*k+2)*(3*k+1) := by
  let n := 3*(j+k+1)
  have h0 := Nat.choose_succ_right_eq n (3*j)
  have h1 := Nat.choose_succ_right_eq n (3*j+1)
  have h2 := Nat.choose_succ_right_eq n (3*j+2)
  rw [show n-(3*j)=3*(k+1) by dsimp [n]; omega] at h0
  rw [show n-(3*j+1)=3*k+2 by dsimp [n]; omega] at h1
  rw [show n-(3*j+2)=3*k+1 by dsimp [n]; omega] at h2
  apply Nat.eq_of_mul_eq_mul_left (by decide : 0<3)
  change 3*(n.choose (3*(j+1))*(j+1)*(3*j+2)*(3*j+1))=3*(n.choose (3*j)*(k+1)*(3*k+2)*(3*k+1))
  calc
    _ = (n.choose (3*j+2+1)*(3*j+2+1))*(3*j+2)*(3*j+1) := by rw [show 3*(j+1)=3*j+2+1 by omega]; ring
    _ = (n.choose (3*j+1+1)*(3*j+1+1))*(3*j+1)*(3*k+1) := by rw [h2]; ring
    _ = (n.choose (3*j+1)*(3*j+1))*(3*k+2)*(3*k+1) := by rw [h1]; ring
    _ = _ := by rw [h0]; ring

theorem mass_step (j k : Nat) :
    mass (j+k+1) (j+1)*(j+1)*(6*k+1)*(6*k+5)=
    mass (j+k+1) j*(k+1)*(6*j+1)*(6*j+5) := by
  have choose := three_choose j k
  let m := j+k+1
  have eq : (((3*m).choose (3*(j+1)):Nat):ℚ)*(j+1)*(3*j+2)*(3*j+1)=
      (((3*m).choose (3*j):Nat):ℚ)*(k+1)*(3*k+2)*(3*k+1) := by exact_mod_cast choose
  unfold mass
  rw [show j+k+1-(j+1)=k by omega,show j+k+1-j=k+1 by omega,two_ways j,two_ways k]
  push_cast
  change _ = _
  simp only [div_eq_mul_inv]
  let common : ℚ := ((6*(j+k+1)-1:Nat):ℚ)*(6*j+5)*(6*j+1)*(6*k+1)*(6*k+5)*ways (2*j)*ways (2*k)*(ways (2*m):ℚ)⁻¹
  calc
    _ = common*((((3*m).choose (3*(j+1)):Nat):ℚ)*(j+1)*(3*j+2)*(3*j+1)) := by unfold common m; ring
    _ = _ := by rw [eq]; unfold common m; ring

theorem mass_nonneg (m j : Nat) : 0≤mass m j := by
  unfold mass
  exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

private theorem decreasing_step (j k : Nat) (jk : j≤k) : mass (j+k+1) (j+1)≤mass (j+k+1) j := by
  have h := mass_step j k
  have cmp : ((k:ℚ)+1)*(6*j+1)*(6*j+5) ≤ ((j:ℚ)+1)*(6*k+1)*(6*k+5) := by
    obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le jk
    push_cast
    nlinarith only [show (0:ℚ)≤d*(36*(j:ℚ)*(j+d)+36*(j+d)+36*j+31) by positivity]
  have hp : (0:ℚ)<((j:ℚ)+1)*(6*k+1)*(6*k+5) := by positivity
  apply le_of_mul_le_mul_right (a:=((j:ℚ)+1)*(6*k+1)*(6*k+5)) _ hp
  simp only [←mul_assoc]
  rw [h]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left cmp (mass_nonneg _ _)

theorem decreasing (m i j : Nat) (le : i≤j) (half : 2*j≤m) : mass m j≤mass m i := by
  induction j with
  | zero =>
    have e : i=0 := by omega
    rw [e]
  | succ j ih =>
    by_cases eq : i=j+1
    · simp [eq]
    have step := decreasing_step j (m-j-1) (by omega)
    rw [show j+(m-j-1)+1=m by omega] at step
    exact step.trans (ih (by omega) (by omega))

private theorem mass_zero (m : Nat) : mass m 0=(6*m-1:Nat) := by
  have hp : (ways (2*m):ℚ)≠0 := by exact_mod_cast (ways_pos _).ne'
  simp [mass,ways,mul_div_cancel_right₀ _ hp]

theorem first_mass (m : Nat) (pos : 0<m) : mass m 1*(6*m-5)=5*m := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt pos)
  have eq := mass_step 0 k
  simp only [Nat.zero_add,zero_add,Nat.cast_zero,zero_mul,zero_add,mul_one,one_mul,Nat.cast_one] at eq
  rw [mass_zero,show 6*(k+1)-1=6*k+5 by omega] at eq
  push_cast at eq ⊢
  apply mul_right_cancel₀ (b:=(6*(k:ℚ)+5)) (by positivity)
  nlinarith only [eq]

end WildSieve.EvenTriples
