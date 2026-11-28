import GraphRule
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace WildSieve.Geometric
open Finset

def rate (m : Nat) : ℚ := 1+2/(m:ℚ)

def peak (w : Fin 3 → Nat) := max (w 0) (max (w 1) (w 2))

private theorem below_peak (w : Fin 3 → Nat) (i : Fin 3) : w i≤peak w := by
  rcases (show i=0 ∨ i=1 ∨ i=2 from (by omega : i.val=0 ∨ i.val=1 ∨ i.val=2).imp
    (fun h => Fin.ext h) (fun h => h.imp (fun h => Fin.ext h) (fun h => Fin.ext h))) with rfl|rfl|rfl
  · exact le_max_left ..
  · exact (le_max_left ..).trans (le_max_right ..)
  · exact (le_max_right ..).trans (le_max_right ..)

private theorem peak_is (w : Fin 3 → Nat) : peak w=w 0 ∨ peak w=w 1 ∨ peak w=w 2 := by
  unfold peak
  rcases max_choice (w 0) (max (w 1) (w 2)) with e|e
  · exact Or.inl e
  · exact Or.inr ((max_choice (w 1) (w 2)).imp (fun z => e.trans z) (fun z => e.trans z))

private theorem largest_le (r : Fin 3 → CutRow) (w : Fin 3 → Nat) (l M : Nat) (ok : ∀ i,w i≤M) :
    largestCosts r w l≤l*M := by
  have zero (i : Fin 3) : w i-peak w=0 := Nat.sub_eq_zero_of_le (below_peak w i)
  have p : priced r w l (peak w)=l*peak w := by simp [priced,zero]
  have plenty : peak w≤M := max_le (ok _) (max_le (ok _) (ok _))
  apply le_trans _ (Nat.mul_le_mul_left l plenty)
  rw [←p]
  rcases peak_is w with q|q|q <;> rw [q] <;> unfold largestCosts <;> omega

private theorem all_mono (r : CutRow) {u v : Nat} (uv : u≤v) (s : Nat) : rowAll r s u≤rowAll r s v := by
  unfold rowAll
  split <;> simp only [←Nat.choose_eq_fast_choose,le_refl]
  apply Nat.choose_le_choose
  exact min_le_min_left _ (by omega)

private theorem special_mono (r : CutRow) {u v : Nat} (uv : u≤v) (s : Nat) :
    rowSpecial r s u≤rowSpecial r s v := by
  unfold rowSpecial
  split
  · rfl
  · exact all_mono r uv s

private theorem regular_mono (r : CutRow) {u v : Nat} (uv : u≤v) (s : Nat) :
    rowRegular r s u≤rowRegular r s v := by
  have pool : min r.pairs ((u-r.forced)/2)≤min r.pairs ((v-r.forced)/2) := min_le_min_left _ (by omega)
  unfold rowRegular
  dsimp
  split
  · rename_i h
    rw [if_pos ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.trans_le pool⟩]
    simp only [←Nat.choose_eq_fast_choose]
    exact Nat.choose_le_choose _ (by omega)
  · exact Nat.zero_le _

/-- A degree bound independent of the remaining set of vertices. The
first term counts every cut. The second separates the forced vertex of
a color from a vertex in an ordinary matching pair. -/
def rowCap (n N b d s : Nat) :=
  let r := rowData n N b d
  min (totalFor n N b d s N)
    (d*peak (fun i => rowSpecial (r i) s N)+(N-1)*peak (fun i => rowRegular (r i) s N))

theorem improved_le_cap (n N b d s u : Nat) (hu : u≤N) :
    improvedDegree n N b d s u≤rowCap n N b d s := by
  have old : improvedDegree n N b d s u≤degreeFor n N b d s u := by
    unfold improvedDegree;dsimp only;split <;> omega
  apply old.trans
  unfold degreeFor rowCap
  dsimp only
  split
  · apply Nat.le_min.mpr
    constructor
    · exact (min_le_left ..).trans (sum_le_sum fun i _ => Nat.mul_le_mul_left _ (all_mono _ hu s))
    · apply (min_le_right ..).trans
      apply Nat.add_le_add
      · exact largest_le _ _ _ _ (fun i => (special_mono _ hu s).trans (below_peak (fun i => rowSpecial (rowData n N b d i) s N) i))
      · exact (largest_le _ _ _ _ (fun i => (regular_mono _ hu s).trans (below_peak (fun i => rowRegular (rowData n N b d i) s N) i))).trans
          (Nat.mul_le_mul_right _ (by omega))
  · exact Nat.zero_le _

def degree (n f t j : Nat) := ((widths f t j).map fun d => rowCap n (3*t) (f+1) d (3*j)).sum

theorem degree_le (n f t u j : Nat) (hu : u≤3*t) : degBound n f t u j≤degree n f t j := by
  unfold degBound degree
  generalize widths f t j=w
  induction w with
  | nil => rfl
  | cons d w ih => exact Nat.add_le_add (improved_le_cap _ _ _ _ _ _ hu) ih

/-- A single geometric rate gives a finite sieve certificate for every
remaining cardinality simultaneously. -/
theorem cert (n f t : Nat) (b : ℚ) (one : 1≤b)
    (localSum : (degree n f t 1:ℚ)*sealWeight t 1*b^3+(degree n f t 2:ℚ)*sealWeight t 2*b^6≤b-1)
    (endSum : (∑ j∈longLevels t,(countBound n f t j:ℚ)*sealWeight t j*b^(3*j))<1) :
    Cert n f t (fun u => b^(3*t-u)) := by
  have bp : 0<b := by linarith
  refine ⟨fun _ _ => pow_pos bp _,?_,?_⟩
  · intro u pos hu
    have term (j : Nat) : (degBound n f t u j:ℚ)*(sealWeight t j*b^(3*t-(u-3*j)))≤
        ((degree n f t j:ℚ)*sealWeight t j*b^(3*j))*b^(3*t-u) := by
      rw [mul_assoc _ (b^(3*j)),←pow_add]
      have powle : b^(3*t-(u-3*j))≤b^(3*j+(3*t-u)) := pow_le_pow_right₀ one (by omega)
      have w : 0≤sealWeight t j := div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
      rw [←mul_assoc]
      exact mul_le_mul (mul_le_mul_of_nonneg_right (by exact_mod_cast degree_le n f t u j hu) w)
        powle (pow_nonneg bp.le _) (mul_nonneg (Nat.cast_nonneg _) w)
    have sum := add_le_add (term 1) (term 2)
    rw [←add_mul] at sum
    have bnd := mul_le_mul_of_nonneg_right localSum (pow_nonneg bp.le (3*t-u))
    simp only [shortLevels,sum_insert (by decide : (1:Nat)∉({2}:Finset Nat)),sum_singleton]
    rw [show 3*t-(u-1)=(3*t-u)+1 by omega,pow_succ]
    exact sum.trans (by simpa only [Nat.reduceMul,sub_mul,one_mul,mul_comm b] using bnd)
  · dsimp only
    rw [Nat.sub_self,pow_zero]
    apply lt_of_le_of_lt _ endSum
    apply sum_le_sum
    intro j hj
    have hj' := mem_range.mp (mem_filter.mp hj).1
    rw [show 3*t-(3*t-3*j)=3*j by omega,mul_assoc]

end WildSieve.Geometric
