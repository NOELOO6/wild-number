import FrozenLayout
import Mathlib.Tactic.FieldSimp

namespace WildSieve
open Finset

def fixedSize (n : Nat) := if n%3=0 then 0 else if n%3=1 then 4 else 5
def levels (n : Nat) := (n-fixedSize n)/3
def numerator (t j : Nat) := ways j * ways (t-j)

/-- A comparison sequence of integers. All checks below multiply out the
common positive denominator, so rounding cannot certify a false inequality. -/
def comparisonTable (degree : Nat → Nat → Nat) (t : Nat) : Array Nat := Id.run do
  let den := ways t
  let mut a : Array Nat := #[10^16]
  for u in [1:3*t+1] do
    let charge := degree u 1 * numerator t 1 * a[u-3]! +
      degree u 2 * numerator t 2 * a[u-6]!
    a := a.push ((den*a[u-1]! - charge)/den)
  return a

def makeTable (n f t : Nat) := comparisonTable (degBound n f t) t

def tableAt (a : Array Nat) (u : Nat) : Nat := a[u]?.getD 0

def DegreeOK (degree : Nat → Nat → Nat) (t : Nat) (a : Array Nat) (u : Nat) : Prop :=
  0<tableAt a u ∧ (0<u →
    (∑ j∈shortLevels,degree u j * numerator t j * tableAt a (u-3*j)) +
      ways t * tableAt a u ≤ ways t * tableAt a (u-1))

instance (degree : Nat → Nat → Nat) (t : Nat) (a : Array Nat) (u : Nat) : Decidable (DegreeOK degree t a u) := by
  unfold DegreeOK
  infer_instance

abbrev LocalOK (n f t : Nat) := DegreeOK (degBound n f t) t

def TailOK (n f t : Nat) (a : Array Nat) : Prop :=
  (∑ j∈longLevels t,countBound n f t j * numerator t j * tableAt a (3*t-3*j)) <
    ways t * tableAt a (3*t)

instance (n f t : Nat) (a : Array Nat) : Decidable (TailOK n f t a) := by
  unfold TailOK
  infer_instance

def accepts (n : Nat) : Bool :=
  let f := fixedSize n
  let t := levels n
  let a := makeTable n f t
  (List.range (3*t+1)).all (fun u => decide (LocalOK n f t a u)) && decide (TailOK n f t a)

theorem weighted (t : Nat) (J : Finset Nat) (c H : Nat → Nat) :
    ∑ j∈J,(c j : ℚ)*(sealWeight t j*(H j : ℚ)) =
      (↑(∑ j∈J,c j * numerator t j * H j) : ℚ)/(ways t : ℚ) := by
  push_cast
  rw [div_eq_mul_inv,Finset.sum_mul]
  apply sum_congr rfl
  intro j _
  simp only [sealWeight,numerator,Nat.cast_mul,div_eq_mul_inv]
  ac_rfl

def tablePasses (n f t : Nat) (a : Array Nat) : Bool :=
  (List.range (3*t+1)).all (fun u => decide (LocalOK n f t a u)) && decide (TailOK n f t a)

theorem local_of_checks (degree : Nat → Nat → Nat) (t : Nat) (a : Array Nat)
    (loc : (List.range (3*t+1)).all (fun u => decide (DegreeOK degree t a u))=true) :
    (∀ u≤3*t,0<(tableAt a u : ℚ)) ∧ (∀ u,0<u → u≤3*t →
      ∑ j∈shortLevels,(degree u j : ℚ)*(sealWeight t j*(tableAt a (u-3*j) : ℚ)) ≤
        (tableAt a (u-1) : ℚ)-tableAt a u) := by
  let v := tableAt a
  have localAt (u) (le : u≤3*t) : DegreeOK degree t a u :=
    of_decide_eq_true (List.all_eq_true.mp loc u (List.mem_range.mpr (by omega)))
  have hp : 0<(ways t : ℚ) := by exact_mod_cast ways_pos t
  constructor
  · intro u hu
    exact_mod_cast (localAt u hu).1
  · intro u pos le
    have check := (localAt u le).2 pos
    change (∑ j∈shortLevels,(_ : ℚ)*(sealWeight t j*(v (u-3*j) : ℚ))) ≤ (v (u-1) : ℚ)-v u
    rw [weighted,div_le_iff₀ hp]
    have rat : (↑(∑ j∈shortLevels,degree u j * numerator t j * v (u-3*j)) : ℚ) +
        (ways t : ℚ)*v u ≤ (ways t : ℚ)*v (u-1) := by exact_mod_cast check
    linarith only [rat]

/-- Any supplied table that passes gives a mathematical certificate. -/
theorem cert_of_table (n f t : Nat) (a : Array Nat) (yes : tablePasses n f t a=true) :
    Cert n f t (fun u => (tableAt a u : ℚ)) := by
  let v := tableAt a
  obtain ⟨loc,endVal⟩ := Bool.and_eq_true_iff.mp yes
  obtain ⟨pos,budget⟩ := local_of_checks (degBound n f t) t a loc
  have hp : 0<(ways t : ℚ) := by exact_mod_cast ways_pos t
  refine ⟨pos,budget,?_⟩
  have check : TailOK n f t a := of_decide_eq_true endVal
  change (∑ j∈longLevels t,(_ : ℚ)*(sealWeight t j*(v (3*t-3*j) : ℚ))) < (v (3*t) : ℚ)
  rw [weighted,div_lt_iff₀ hp]
  rw [mul_comm (v (3*t) : ℚ)]
  exact_mod_cast check

theorem cert_of_accepts (n : Nat) (yes : accepts n=true) :
    ∃ h,Cert n (fixedSize n) (levels n) h :=
  ⟨_,cert_of_table n _ _ _ yes⟩

#print axioms cert_of_accepts
end WildSieve
