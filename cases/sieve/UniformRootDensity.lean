import RootDensity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace WildSieve.RootDensity
open Finset TripleIncidence WildExact
local instance (priority := 2000) uniformEq {n : Nat} : DecidableEq (Fin n) := (inferInstance : LinearOrder (Fin n)).toDecidableEq

private theorem endpoint_minimum (b e m k g h p : Nat) (cap : h≤m)
    (pairs : h*(h+2)≤p+h*k) (slope : (2*m+2)*g≤6*b*e+k*g) :
    m*(m+2)*g+6*h*b*e≤p*g+m*k*g+6*m*b*e := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le cap
  have tangent := Nat.mul_le_mul_left d slope
  have lower := Nat.mul_le_mul_right g pairs
  nlinarith only [tangent,lower,Nat.zero_le (d*d*g)]

/-- Multiply by the number of partitions of the remaining 6s+6 vertices
to obtain the lower bound for the number of partitions avoiding the given triples. -/
def densityCoefficient (s : Nat) :=
  20440+s*(90114+s*(158640+s*(144018+s*(71496+s*(18468+s*1944)))))

private theorem odd_choose (j : Nat) : (2*j+1).choose 2=(2*j+1)*j := by
  rw [Nat.choose_two_right,show 2*j+1-1=2*j by omega,
    show (2*j+1)*(2*j)=((2*j+1)*j)*2 by ring,Nat.mul_div_cancel _ (by decide : 0<2)]

private theorem even_choose (j : Nat) : (2*j+2).choose 2=(j+1)*(2*j+1) := by
  rw [Nat.choose_two_right,show 2*j+2-1=2*j+1 by omega,
    show (2*j+2)*(2*j+1)=(j+1)*(2*j+1)*2 by ring,Nat.mul_div_cancel _ (by decide : 0<2)]

/-- At every odd triple order from fifteen onward, at least 146 out of every
1001 partitions avoid any forbidden triple family of maximum pair degree three. -/
private theorem clear_bounds (s : Nat) (H : Finset (Finset (Fin (6*s+15))))
    (size : ∀ A∈H,A.card=3) (cap : PairBound H 3) :
    146*ways (2*s+5) ≤ 1001*(clear H).card ∧ densityCoefficient s*ways (2*s+2)≤(clear H).card ∧
      s*ways (2*s+5)≤3*(s+1)*(clear H).card := by
  let a := (3*s+7)*(6*s+13)
  let b := (6*s+11)*(3*s+5)
  let e := (3*s+4)*(6*s+7)
  let j := (6*s+9)*(3*s+4)
  let m := (6*s+15)*(3*s+7)
  let k := 27*s+57
  let g := (3*s+4)*(12*s+12)
  let w := ways (2*s+2)
  have scale : 3*e=j+g := by dsimp [e,j,g]; ring
  have maxH : H.card≤m := by
    have h := within_bound H size 3 cap univ
    have all : within H univ=H := by ext; simp [within]
    have val : (6*s+15).choose 2=m := by
      rw [show 6*s+15=2*(3*s+7)+1 by omega,odd_choose]
      dsimp [m]; ring
    rw [all,card_univ,Fintype.card_fin,val] at h
    omega
  have we : ways (2*s+3)=e*w := by
    change Nat.fast_choose (3*(2*s+2)+2) 2*w=_
    rw [←Nat.choose_eq_fast_choose,show 3*(2*s+2)+2=2*(3*s+3)+2 by omega,even_choose]
    dsimp [e]; ring
  have wb : ways (2*s+4)=b*e*w := by
    change Nat.fast_choose (3*(2*s+3)+2) 2*ways (2*s+3)=_
    rw [←Nat.choose_eq_fast_choose,show 3*(2*s+3)+2=2*(3*s+5)+1 by omega,odd_choose,we]
    dsimp [b]; ring
  have wa : ways (2*s+5)=a*b*e*w := by
    change Nat.fast_choose (3*(2*s+4)+2) 2*ways (2*s+4)=_
    rw [←Nat.choose_eq_fast_choose,show 3*(2*s+4)+2=2*(3*s+6)+2 by omega,even_choose,wb]
    dsimp [a]; ring
  have rest : (6*s+15-6).choose 2=j := by
    rw [show 6*s+15-6=2*(3*s+4)+1 by omega,odd_choose]
    dsimp [j]; ring
  obtain ⟨p,lo,_,hi⟩ := density_budget_full (2*s+5) 3 (by omega) H size cap
  have pairs : H.card*(H.card+2)≤p+H.card*k := by
    have kEq : 1+3*(6*s+15-3)*3/2+2=k := by dsimp [k]; omega
    rw [←kEq,Nat.mul_add,Nat.mul_add]
    omega
  have tangent : (2*m+2)*g≤6*b*e+k*g := by dsimp [m,g,b,e,k]; ring_nf; omega
  rw [wa,show 2*s+5-1=2*s+4 by omega,wb,show 2*s+5-2=2*s+3 by omega,we,
    show 2*s+5-3=2*s+2 by omega,rest,show 3*j/3=j by omega] at hi
  rw [wa]
  have saved := congrArg (fun z => p*z*w) scale
  change _ ≤ _+_+p*(j*w) at hi
  have low := Nat.mul_le_mul_right w (endpoint_minimum b e m k g _ _ maxH pairs tangent)
  have poly : 6*a*b*e+m*(m+2)*g=6*densityCoefficient s+6*m*b*e+m*k*g := by
    dsimp [a,b,e,m,k,g,densityCoefficient]; ring
  have eq := congrArg (fun z => z*w) poly
  have count : densityCoefficient s*w≤(clear H).card := by
    nlinarith only [low,hi,saved,eq]
  have scaled (x y : Nat) (hxy : x*(a*b*e)≤y*densityCoefficient s) :
      x*(a*b*e*w) ≤ y*(clear H).card := by
    calc
      x*(a*b*e*w) = (x*(a*b*e))*w := by ring
      _ ≤ (y*densityCoefficient s)*w := Nat.mul_le_mul_right w hxy
      _ = y*(densityCoefficient s*w) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ count
  refine ⟨scaled _ _ ?_,count,scaled _ _ ?_⟩ <;> dsimp [a,b,e,densityCoefficient] <;> ring_nf <;> omega

theorem uniform_clear (s : Nat) (H : Finset (Finset (Fin (6*s+15))))
    (size : ∀ A∈H,A.card=3) (cap : PairBound H 3) :
    146*ways (2*s+5)≤1001*(clear H).card := (clear_bounds s H size cap).1

theorem quantitative_clear (s : Nat) (H : Finset (Finset (Fin (6*s+15))))
    (size : ∀ A∈H,A.card=3) (cap : PairBound H 3) :
    densityCoefficient s*ways (2*s+2)≤(clear H).card := (clear_bounds s H size cap).2.1

theorem uniform_sealed (s : Nat) (g : Coloring (6*s+15) (6*s+15)) :
    146*ways (2*s+5)≤1001*(clear (sealed g)).card :=
  uniform_clear s (sealed g) (fun _ h => (mem_sealed.mp h).1) (pair_bound g (by omega))

theorem quantitative_sealed (s : Nat) (g : Coloring (6*s+15) (6*s+15)) :
    densityCoefficient s*ways (2*s+2)≤(clear (sealed g)).card :=
  quantitative_clear s (sealed g) (fun _ h => (mem_sealed.mp h).1) (pair_bound g (by omega))

/-- The fraction surviving all single-triple cuts is at least s/(3(s+1)). -/
theorem rate_sealed (s : Nat) (g : Coloring (6*s+15) (6*s+15)) :
    s*ways (2*s+5)≤3*(s+1)*(clear (sealed g)).card :=
  (clear_bounds s (sealed g) (fun _ h => (mem_sealed.mp h).1) (pair_bound g (by omega))).2.2

theorem fifteen_crossing (g : Coloring 15 15) : 204400≤(clear (sealed g)).card := by
  simpa only [show densityCoefficient 0*ways (2*0+2)=204400 by decide] using quantitative_sealed 0 g

#print axioms fifteen_crossing
#print axioms rate_sealed
#print axioms quantitative_sealed
#print axioms uniform_sealed
end WildSieve.RootDensity
