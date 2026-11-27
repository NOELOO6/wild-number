import ExactRange
import TrimmedLayout
import JointScopes
namespace WildSieve
open Finset WildExact

private def jointCharge (n t : Nat) (a : Array Nat) (u b : Nat) :=
  jointDegree n t u b 1 * numerator t 1 * tableAt a (u-3) +
  jointDegree n t u b 2 * numerator t 2 * tableAt a (u-6)

private def comparisonJoint (n t : Nat) : Array Nat := Id.run do
  let den := ways t
  let mut a := #[10^16]
  for u in [1:3*t+1] do
    let charge := ((List.range (jointLimit n u+1)).map (jointCharge n t a u)).foldl max 0
    a := a.push ((den*a[u-1]! - charge)/den)
  return a

open Lean Elab Term in
elab "jointTable%(" n:num "," t:num ")" : term => do
  return toExpr (comparisonJoint n.getNat t.getNat)

private def jointCheck (n t : Nat) (a : Array Nat) (u : Nat) :=
  decide (0<tableAt a u) && (u==0 || (List.range (jointLimit n u+1)).all (fun b =>
    decide (jointCharge n t a u b + ways t * tableAt a u ≤ ways t * tableAt a (u-1))))

private def tailCheck (n t : Nat) (a : Array Nat) := decide
  ((∑ j∈longLevels t,trimmedCount n 0 t j * ways (t-j) * tableAt a (3*t-3*j)) <
    ways t * tableAt a (3*t))

private theorem joint_checks (n t : Nat) (a : Array Nat)
    (localChecks : (List.range (3*t+1)).all (jointCheck n t a)=true) :
    (∀ u≤3*t,0<(tableAt a u:ℚ)) ∧ (∀ u,0<u → u≤3*t → ∀ b≤jointLimit n u,
      (∑ j∈shortLevels,(jointDegree n t u b j : ℚ)*(sealWeight t j*(tableAt a (u-3*j) : ℚ)))
        ≤ (tableAt a (u-1):ℚ)-tableAt a u) := by
  have every u (le : u≤3*t) := Bool.and_eq_true_iff.mp
    (List.all_eq_true.mp localChecks u (List.mem_range.mpr (by omega)))
  constructor
  · intro u le
    exact_mod_cast of_decide_eq_true (every u le).1
  · intro u pos le b small
    have all := (Bool.or_eq_true_iff.mp (every u le).2).resolve_left (by simp [Nat.ne_of_gt pos])
    have chk := of_decide_eq_true (List.all_eq_true.mp all b (List.mem_range.mpr (by omega)))
    have rat : (↑(∑ j∈shortLevels,jointDegree n t u b j * numerator t j * tableAt a (u-3*j)):ℚ) +
        (ways t:ℚ)*tableAt a u ≤ (ways t:ℚ)*tableAt a (u-1) := by
      have eq : (∑ j∈shortLevels,jointDegree n t u b j*numerator t j*tableAt a (u-3*j))=jointCharge n t a u b := by
        simp [shortLevels,jointCharge]
      rw [eq]
      exact_mod_cast chk
    rw [weighted,div_le_iff₀ (show (0:ℚ)<ways t by exact_mod_cast ways_pos t)]
    linarith only [rat]

private theorem tail_checks (n t : Nat) (a : Array Nat) (yes : tailCheck n t a=true) :
    (∑ j∈longLevels t,(trimmedCount n 0 t j:ℚ)*((ways (t-j):ℚ)/ways t*(tableAt a (3*t-3*j):ℚ))) <
        (tableAt a (3*t):ℚ) := by
  have h := of_decide_eq_true yes
  have hp : 0<(ways t : ℚ) := by exact_mod_cast ways_pos t
  have scale : ∀ j,(trimmedCount n 0 t j : ℚ) * ((ways (t-j):ℚ)/ways t*(tableAt a (3*t-3*j):ℚ)) =
    (↑(trimmedCount n 0 t j * ways (t-j) * tableAt a (3*t-3*j)):ℚ)/(ways t:ℚ) := by
    intro j
    push_cast
    simp only [div_eq_mul_inv]
    ac_rfl
  simp only [scale]
  simp only [div_eq_mul_inv,←Finset.sum_mul,←Nat.cast_sum]
  rw [←div_eq_mul_inv,div_lt_iff₀ hp,mul_comm (tableAt a (3*t) : ℚ)]
  exact_mod_cast h

local instance (priority := 2000) jointExactFinEq {m : Nat} : DecidableEq (Fin m) :=
  (inferInstance : LinearOrder (Fin m)).toDecidableEq
set_option maxRecDepth 200000
set_option maxHeartbeats 0

private def certificate := jointTable%(81,27)
private theorem localEnough : (List.range 82).all (jointCheck 81 27 certificate)=true := by decide
private theorem tailEnough : tailCheck 81 27 certificate=true := by decide

/-- Every minimum proper coloring of K81 and K82 has wild number 54. -/
theorem exact_K81_K82 : (∀ g : Coloring 81 81,Exact g 54) ∧ (∀ g : Coloring 82 81,Exact g 54) := by
  obtain ⟨pos,loc⟩ := joint_checks 81 27 certificate localEnough
  have tail := tail_checks 81 27 certificate tailEnough
  apply exact_from_rule 81 (by decide) (by decide)
  intro F B r hr bs ws rain
  apply frozen_trimmed_actual F B r 0 27 hr bs ws rain (Or.inl rfl) _ pos _ (by simpa only [Fintype.card_fin] using tail)
  intro U z hz
  obtain ⟨b,cap,d⟩ := joint_scope_bounds F B r hr 27 bs ws rain U z hz
  have le : U.card≤3*27 := U.card_le_univ.trans_eq ((Fintype.card_coe Bᶜ).trans ws)
  apply le_trans _ (loc U.card (card_pos.mpr ⟨z,hz⟩) le b cap)
  apply sum_le_sum
  intro j hj
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast d j hj)
    (mul_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
      (pos _ ((Nat.sub_le _ _).trans le)).le)

#print axioms exact_K81_K82
end WildSieve
