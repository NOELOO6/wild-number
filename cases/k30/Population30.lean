import CutModel30
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace WildSieve.Thirty
open Finset

/-- The type of a color is the number of its matching edges in the twelve-set. -/
structure Population (X : Fin 7 → ℚ) : Prop where
  positive : ∀ i, 0≤X i
  colors : ∑ i, X i=29
  edges : ∑ i, i.val*X i=66
  anchor : 1≤X 6

def lineSlope (upper : Bool) (t : Nat) : ℚ :=
  if upper then (match t with | 0 => 5/231 | 1 => -13/3740 | _ => 415/37128)
  else (match t with | 0 => 1/154 | 1 => -4/935 | _ => 25/3094)

def lineIntercept (upper : Bool) (t : Nat) : ℚ :=
  if upper then (match t with | 0 => 0 | 1 => 1/34 | _ => 5/6188)
  else (match t with | 0 => -1/77 | 1 => 24/935 | _ => -25/3094)

def populationSlope (i : Nat) : ℚ :=
  match i with
  | 0 => -1/6 | 1 => -1/5 | 2 => -1/4 | _ => 1/(i : ℚ)

def populationIntercept (i : Nat) : ℚ :=
  if i<3 then 6/((6-i : Nat) : ℚ) else 0

private theorem lines : ∀ t : Fin 3, ∀ i : Fin 7,
    (lineSlope false t*i.val + lineIntercept false t ≤ first t i ∧
      first t i ≤ lineSlope true t*i.val + lineIntercept true t) ∧
    (lineSlope false t*60+lineIntercept false t*28+first t 6=5*lowMean t ∧
     lineSlope true t*60+lineIntercept true t*28+first t 6=highMean t) := by native_decide

private theorem coordinate_lines : ∀ i j : Fin 7,
    ((if i=j then 1 else 0 : ℚ) ≤ populationSlope i*j.val+populationIntercept i) ∧
    populationSlope i*60+populationIntercept i*28+(if i=6 then 1 else 0)=highPopulation i := by
  native_decide

/-- Set aside the closing anchor, leaving 28 colors and 60 internal edges. -/
private def rest (X : Fin 7 → ℚ) (i : Fin 7) := X i - if i=6 then 1 else 0

private theorem rest_pos {X : Fin 7 → ℚ} (P : Population X) (i : Fin 7) : 0≤rest X i := by
  by_cases h : i=6
  · subst i; simpa [rest] using P.anchor
  · simpa [rest,h] using P.positive i

private theorem sum_rest (X f : Fin 7 → ℚ) :
    ∑ i, f i*rest X i = (∑ i,f i*X i)-f 6 := by
  simp [rest,mul_sub,Finset.sum_sub_distrib,mul_ite]

private theorem affine_rest {X : Fin 7 → ℚ} (P : Population X) (a b : ℚ) :
    ∑ i : Fin 7, (a*i.val+b)*rest X i=a*60+b*28 := by
  have colors := sum_rest X (fun _ => 1)
  simp only [one_mul,P.colors] at colors
  have edges := sum_rest X (fun i => (i.val : ℚ))
  rw [P.edges] at edges
  change _ = 66 - (6 : ℚ) at edges
  norm_num at edges colors
  simp only [add_mul,mul_assoc,Finset.sum_add_distrib,←Finset.mul_sum,edges,colors]

theorem population_mean_bounds {X : Fin 7 → ℚ} (P : Population X) (t : Fin 3) :
    5*lowMean t ≤ ∑ i : Fin 7,first t i*X i ∧
      (∑ i : Fin 7,first t i*X i) ≤ highMean t := by
  have low := sum_le_sum (s:=univ) (fun i _ => mul_le_mul_of_nonneg_right
    ((lines t i).1.1) (rest_pos P i))
  have high := sum_le_sum (s:=univ) (fun i _ => mul_le_mul_of_nonneg_right
    ((lines t i).1.2) (rest_pos P i))
  rw [affine_rest P,sum_rest] at low
  rw [affine_rest P,sum_rest] at high
  simp only [show ((6 : Fin 7) : Nat) = 6 by decide] at low high
  obtain ⟨a,b⟩ := (lines t 0).2
  constructor <;> linarith

theorem population_bounds {X : Fin 7 → ℚ} (P : Population X) (i : Fin 7) :
    lowPopulation i≤X i ∧ X i≤highPopulation i := by
  have high := sum_le_sum (s:=univ) (fun j _ => mul_le_mul_of_nonneg_right
    ((coordinate_lines i j).1) (rest_pos P j))
  rw [affine_rest P] at high
  simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,mem_univ,ite_true] at high
  have value := (coordinate_lines i 0).2
  by_cases h : i=6
  · subst i
    simp only [rest,ite_true] at high value
    exact ⟨P.anchor,by linarith⟩
  · have ne : i.val ≠ 6 := fun eq => h (Fin.ext eq)
    simp only [rest,if_neg h] at high value
    exact ⟨by simpa [lowPopulation,ne] using P.positive i,by linarith⟩

/-- The four product constraints used to control the joint moment of a color
population and a conditional hit count. -/
theorem product_bounds (x y l h a b : ℚ) (xl : l≤x) (xh : x≤h) (ya : a≤y) (yb : y≤b) :
    (l*y+a*x-l*a≤x*y) ∧ (h*y+b*x-h*b≤x*y) ∧
    (x*y≤l*y+b*x-l*b) ∧ (x*y≤h*y+a*x-h*a) := by
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr xl) (sub_nonneg.mpr ya)]
  refine ⟨?_,?_,?_⟩
  · nlinarith [mul_nonneg (sub_nonneg.mpr xh) (sub_nonneg.mpr yb)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr xl) (sub_nonneg.mpr yb)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr xh) (sub_nonneg.mpr ya)]

end WildSieve.Thirty
