import FilteredMoments
import MatchingSixes
import GraphSieve
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace WildSieve.TwoTripleDensity
open Finset WildExact
local instance (priority := 2000) {n : Nat} : DecidableEq (Fin n) :=
  (inferInstance : LinearOrder (Fin n)).toDecidableEq
set_option maxHeartbeats 1600000
variable {A C : Type} [LinearOrder A] [Fintype A] [Fintype C]

/-- Layouts of U in which no color closes any two whole triples. -/
noncomputable def clear (F : Factor A C) (U : Finset A) : Finset (Layout U) :=
  univ \ (marks F U).biUnion (localSeal U)

private theorem count_budget (F : Factor A C) (U : Finset A) (t : Nat) (sz : U.card=3*t) (lo : 2≤t) (cap : Nat) (m : (marks F U).card≤cap) :
    ways t≤(clear F U).card+cap*10*ways (t-2) := by
  classical
  let bad := (marks F U).biUnion (localSeal U)
  have book := card_sdiff_add_card_eq_card (subset_univ bad)
  change (clear F U).card+bad.card=(univ : Finset (Layout U)).card at book
  rw [card_univ,card_layout t U sz] at book
  have each (Q : Finset A) (hq : Q∈marks F U) : (localSeal U Q).card=10*ways (t-2) := by
    obtain ⟨sub,six,_⟩ := mark_mem.mp hq
    exact local_seal_card U Q 2 (t-2) sub six (by omega)
  have loss : bad.card≤(marks F U).card*(10*ways (t-2)) := by
    apply card_biUnion_le.trans
    simpa using sum_le_sum (s:=marks F U) (fun Q h => (each Q h).le)
  have paid := Nat.mul_le_mul_right (10*ways (t-2)) m
  rw [Nat.mul_assoc cap 10]
  omega

private theorem double_choose_two (n : Nat) : 2*(n+2).choose 2=(n+2)*(n+1) := by
  have z := Nat.choose_succ_right_eq (n+2) 1
  simpa [Nat.mul_comm] using z

private theorem six_choose_three (n : Nat) : 6*(n+3).choose 3=(n+3)*(n+2)*(n+1) := by
  have z := Nat.choose_succ_right_eq (n+3) 2
  have q := double_choose_two (n+1)
  simp only [Nat.add_sub_cancel,Nat.add_sub_cancel_right] at z
  have eq : n+3-2=n+1 := by omega
  rw [eq] at z
  nlinarith only [z,q,congrArg (fun a => a*(n+1)) q]

private theorem binom_three (n : Nat) : 6*n.choose 3=n*(n-1)*(n-2) := by
  by_cases h : 3≤n
  · obtain ⟨m,hm⟩ := Nat.exists_eq_add_of_le h
    rw [show n=m+3 by omega,show m+3-1=m+2 by omega,show m+3-2=m+1 by omega]
    exact six_choose_three m
  · rcases (show n=0 ∨ n=1 ∨ n=2 by omega) with rfl|rfl|rfl <;> decide

private theorem normalized (e k : Nat) (le : e≤k) : k*e.choose 3≤e*k.choose 3 := by
  have smaller := Nat.mul_le_mul (Nat.sub_le_sub_right le 1) (Nat.sub_le_sub_right le 2)
  have q := Nat.mul_le_mul_left (e*k) smaller
  have x := congrArg (fun z => k*z) (binom_three e)
  have y := congrArg (fun z => e*z) (binom_three k)
  nlinarith only [q,x,y]

omit [Fintype A] in
/-- Each edge of the induced complete graph can pay for only one color.
The estimate is independent of the number of colors in the ambient factorization. -/
theorem marks_from_edges (F : Factor A C) (U : Finset A) (k : Nat) (cap : U.card≤2*k+1) :
    k*(marks F U).card ≤ U.card.choose 2*k.choose 3 := by
  classical
  have union := card_biUnion_le (s:=(univ : Finset C)) (t:=fun c => candidates F c ∅ U 6)
  change (marks F U).card≤_ at union
  simp_rw [candidate_pairs F _ U 3] at union
  apply (Nat.mul_le_mul_left k union).trans
  rw [mul_sum,←sum_inside F U,sum_mul]
  apply sum_le_sum
  intro c _
  have z := ends_bound (F.invol c) U
  change 2*Inside F c U≤U.card at z
  exact normalized _ _ (by omega)

omit [Fintype A] in
private theorem odd_marks (F : Factor A C) (U : Finset A) (k : Nat) (sz : U.card=2*k+1) (pos : 0<k) :
    (marks F U).card≤U.card*k.choose 3 := by
  have bound := marks_from_edges F U k sz.le
  have bin := Nat.choose_succ_right_eq U.card 1
  rw [Nat.choose_one_right,sz,show 2*k+1-1=2*k by omega] at bin
  have eq : U.card.choose 2=U.card*k := by
    rw [sz]; nlinarith only [bin]
  rw [eq,mul_comm U.card k,mul_assoc] at bound
  exact Nat.le_of_mul_le_mul_left bound pos

/-- Uniform lower fraction at every odd triple order n ≥ 21, with its sharper order-dependent bound. -/
theorem uniform (s : Nat) (F : Factor A C) (U : Finset A)
    (uc : U.card=6*s+21) :
    let t := 2*s+7
    let n := 6*s+21
    (n*n-21*n+48)*ways t ≤ 6*(n-2)*(n-4)*(clear F U).card ∧
      8*ways t≤323*(clear F U).card := by
  have marks := odd_marks F U (3*s+10) (by omega) (by omega)
  have book := count_budget F U (2*s+7) (by omega) (by omega) _ marks
  rw [uc] at book
  let w := ways (2*s+5)
  let a := (6*s+20).choose 2
  let b := (6*s+17).choose 2
  have a2 : 2*a=(6*s+20)*(6*s+19) := double_choose_two (6*s+18)
  have b2 : 2*b=(6*s+17)*(6*s+16) := double_choose_two (6*s+15)
  have c3 := six_choose_three (3*s+7)
  have counts : ways (2*s+7)=a*b*w := by
    change Nat.fast_choose (3*(2*s+6)+2) 2*(Nat.fast_choose (3*(2*s+5)+2) 2*w)=_
    simp only [←Nat.choose_eq_fast_choose,show 3*(2*s+6)+2=6*s+20 by omega,
      show 3*(2*s+5)+2=6*s+17 by omega,a,b,Nat.mul_assoc]
  dsimp only
  rw [counts] at book ⊢
  rw [show 2*s+7-2=2*s+5 by omega] at book
  change a*b*w ≤ (clear F U).card + (6*s+21)*(3*s+10).choose 3*10*w at book
  have prod : 4*(a*b)=(6*s+20)*(6*s+19)*((6*s+17)*(6*s+16)) := by
    rw [←a2,←b2]; ring
  have cross : 6*(6*s+19)*(6*s+17)*((6*s+21)*(3*s+10).choose 3*10*w)=
      5*(6*s+21)*(6*s+18)*(a*b*w) := by
    nlinarith only [congrArg (fun q => (6*s+19)*(6*s+17)*(6*s+21)*10*w*q) c3,
                    congrArg (fun q => (3*s+9)*(6*s+21)*5*w*q) prod]
  have sci := Nat.mul_le_mul_left (6*(6*s+19)*(6*s+17)) book
  have hsub : (6*s+21)*(6*s+21)-21*(6*s+21)+48=36*s^2+126*s+48 := by
    have z : (6*s+21)*(6*s+21)=21*(6*s+21)+(36*s^2+126*s) := by ring
    rw [z,Nat.add_sub_cancel_left]
  simp only [show 6*s+21-2=6*s+19 by omega,show 6*s+21-4=6*s+17 by omega,hsub]
  have first : (36*s^2+126*s+48)*(a*b*w)≤6*(6*s+19)*(6*s+17)*(clear F U).card := by
    nlinarith only [sci,cross]
  refine ⟨first,?_⟩
  have scale : 8*(6*(6*s+19)*(6*s+17))≤323*(36*s^2+126*s+48) := by ring_nf; omega
  have p := Nat.mul_le_mul_right (a*b*w) scale
  have q := Nat.mul_le_mul_left 323 first
  have l : (6*(6*s+19)*(6*s+17))*(8*(a*b*w))≤(6*(6*s+19)*(6*s+17))*(323*(clear F U).card) := by
    nlinarith only [p,q]
  have pos : 0<6*(6*s+19)*(6*s+17) := Nat.mul_pos (Nat.mul_pos (by decide) (by omega)) (by omega)
  exact Nat.le_of_mul_le_mul_left (c:=6*(6*s+19)*(6*s+17)) l pos

/-- Even-sized free regions have the same palette-independent bound, with a different fraction. -/
theorem even_region (s : Nat) (F : Factor A C) (U : Finset A) (uc : U.card=6*s+36) :
    let t := 2*s+12
    let u := 6*s+36
    (u-30)*ways t ≤ 6*(u-5)*(clear F U).card ∧ ways t≤31*(clear F U).card := by
  let k := 3*s+18
  have cap := marks_from_edges F U k (by dsimp [k]; omega)
  have e2 := double_choose_two (6*s+34)
  have eEq : U.card.choose 2=k*(6*s+35) := by
    rw [uc]; dsimp [k]; nlinarith only [e2]
  rw [eEq,mul_assoc] at cap
  have marks := Nat.le_of_mul_le_mul_left cap (show 0<k by dsimp [k]; omega)
  have book := count_budget F U (2*s+12) (by omega) (by omega) _ marks
  let w := ways (2*s+10)
  let a := (6*s+35).choose 2
  let b := (6*s+32).choose 2
  have a2 : 2*a=(6*s+35)*(6*s+34) := double_choose_two (6*s+33)
  have b2 : 2*b=(6*s+32)*(6*s+31) := double_choose_two (6*s+30)
  have c3 : 6*k.choose 3=(3*s+18)*(3*s+17)*(3*s+16) := six_choose_three (3*s+15)
  have counts : ways (2*s+12)=a*b*w := by
    change Nat.fast_choose (3*(2*s+11)+2) 2*(Nat.fast_choose (3*(2*s+10)+2) 2*w)=_
    simp only [←Nat.choose_eq_fast_choose,show 3*(2*s+11)+2=6*s+35 by omega,
      show 3*(2*s+10)+2=6*s+32 by omega,a,b,Nat.mul_assoc]
  dsimp only
  rw [counts] at book ⊢
  rw [show 2*s+12-2=2*s+10 by omega] at book
  change a*b*w≤(clear F U).card+(6*s+35)*k.choose 3*10*w at book
  have prod : 4*(a*b)=(6*s+35)*(6*s+34)*((6*s+32)*(6*s+31)) := by rw [←a2,←b2]; ring
  have cross : 6*(6*s+31)*((6*s+35)*k.choose 3*10*w)=5*(6*s+36)*(a*b*w) := by
    nlinarith only [congrArg (fun q => (6*s+31)*(6*s+35)*10*w*q) c3,
                    congrArg (fun q => 5*(3*s+18)*w*q) prod]
  have sci := Nat.mul_le_mul_left (6*(6*s+31)) book
  rw [show 6*s+36-30=6*s+6 by omega,show 6*s+36-5=6*s+31 by omega]
  have first : (6*s+6)*(a*b*w)≤6*(6*s+31)*(clear F U).card := by nlinarith only [sci,cross]
  refine ⟨first,?_⟩
  have scale : 6*(6*s+31)≤31*(6*s+6) := by omega
  have p := Nat.mul_le_mul_right (a*b*w) scale
  have q := Nat.mul_le_mul_left 31 first
  have l : (6*(6*s+31))*(a*b*w)≤(6*(6*s+31))*(31*(clear F U).card) := by nlinarith only [p,q]
  exact Nat.le_of_mul_le_mul_left l (Nat.mul_pos (by decide) (by omega))

/-- Apply the order-dependent fraction directly to a minimum proper coloring. -/
theorem every_coloring (s : Nat) (g : Coloring (6*s+21) (6*s+21)) :
    let n := 6*s+21
    let F := coloringFactor (augment (n:=6*s+21) (by omega) g)
    let U := (univ : Finset (Fin (6*s+21+1))).erase (Fin.last (6*s+21))
    (n*n-21*n+48)*ways (2*s+7) ≤ 6*(n-2)*(n-4)*(clear F U).card ∧
      8*ways (2*s+7)≤323*(clear F U).card := by
  exact uniform s _ _ (by simp)

#print axioms even_region
#print axioms every_coloring
end WildSieve.TwoTripleDensity
