import RowTotals
import Mathlib.Tactic.Linarith

namespace WildSieve
open Finset

private theorem choose_square (a : Nat) : 2*a.choose 2 + a=a*a := by
  have h := Nat.choose_succ_right_eq a 1
  simp only [Nat.choose_one_right] at h
  cases a with
  | zero => decide
  | succ a =>
    change (a+1).choose 2 * 2 = (a+1)*a at h
    nlinarith only [h]

/-- Convexity of the number of unordered pairs between integer endpoints. -/
private theorem choose_chord (a i m : Nat) (le : i≤m) :
    m*((a+i).choose 2) ≤ m*(a.choose 2) + i*((a+m).choose 2 - a.choose 2) := by
  have diff := Nat.sub_add_cancel (Nat.choose_le_choose 2 (Nat.le_add_right a m))
  have x := congrArg (· * m) (choose_square (a+i))
  have y := congrArg (· * m) (choose_square a)
  have z := congrArg (· * i) (choose_square (a+m))
  have w := congrArg (· * i) (choose_square a)
  have q := congrArg (· * i) diff
  have tail := Nat.mul_le_mul_left (m*i) le
  dsimp at x y z w q
  nlinarith only [x,y,z,w,q,tail]

def chordBound (g u : Nat) : Nat :=
  let a := (u-g)/2-1
  let m := g/2
  ((u-1)*m*a.choose 2 + (g.choose 2)*((a+m).choose 2-a.choose 2))/m

def improvedDegree (n N b d s u : Nat) :=
  let old := degreeFor n N b d s u
  let g := N+b-u
  if d=0 ∧ s=6 ∧ g<u ∧ 0<g/2 then min old (chordBound g u) else old

variable {A C : Type} [LinearOrder A] [Fintype A] [Fintype C]

/-- When a pair of triples closes on its own, the outside vertices constrain
all colors at once. Every outside edge contributes to just one matching. -/
theorem six_local (F : Factor A C) (U : Finset A) (z : A) (zu : z∈U)
    (large : Uᶜ.card<U.card) (den : 0<Uᶜ.card/2) :
    ((sides F ∅ U 6).filter (fun X => z∈X)).card ≤ chordBound Uᶜ.card U.card := by
  classical
  let g := Uᶜ.card
  let u := U.card
  let m := g/2
  let a := (u-g)/2-1
  let low := a.choose 2
  let delta := (a+m).choose 2-low
  let fam (c : C) := (candidates F c ∅ U 6).filter (fun X => z∈X)
  let H := (sides F ∅ U 6).filter (fun X => z∈X)
  let S := univ.filter (fun c => (fam c).Nonempty)
  have cover : H ⊆ S.biUnion fam := by
    intro X hx
    obtain ⟨hm,zx⟩ := mem_filter.mp hx
    obtain ⟨c,hc⟩ := side_mem.mp hm
    have xf : X∈fam c := mem_filter.mpr ⟨hc,zx⟩
    exact mem_biUnion.mpr ⟨c,mem_filter.mpr ⟨mem_univ _,X,xf⟩,xf⟩
  have conditions (c) (X) (xf : X∈fam c) : X⊆U ∧ X.card=6 ∧ Closed (F.f c) X ∧ z∈X := by
    obtain ⟨hc,zx⟩ := mem_filter.mp xf
    obtain ⟨sub,sz,closed⟩ := candidate_mem.mp hc
    exact ⟨sub,sz,by simpa using closed,zx⟩
  have sc : S.card≤u-1 := by
    change S.card≤U.card-1
    rw [← card_erase_of_mem zu]
    apply card_le_card_of_injOn (fun c => F.f c z) _ (F.unique z).injOn
    intro c hc
    obtain ⟨X,xh⟩ := (mem_filter.mp hc).2
    obtain ⟨sub,_,closed,zx⟩ := conditions c X xh
    exact mem_erase.mpr ⟨(F.moving c z).symm,sub (closed z zx)⟩
  have per (c : C) : m*(fam c).card ≤ m*low + Inside F c Uᶜ*delta := by
    let i := Inside F c Uᶜ
    have outside := ends_bound (F.invol c) Uᶜ
    change 2*i≤g at outside
    have im : i≤m := by dsimp [m]; omega
    have eq := free_pair_size (F.invol c) (F.moving c) Uᶜ
    rw [compl_compl] at eq
    change 2*Inside F c U=u-(g-2*i) at eq
    have gu : g<u := large
    have key : Inside F c U-1=a+i := by dsimp [a]; omega
    have valid (X) (hx : X∈fam c) :
        X⊆U ∧ X.card=6 ∧ (∅ : Finset A)⊆X ∧ Closed (F.f c) (X \ ∅) ∧ z∈X \ ∅ := by
      obtain ⟨sub,sz,closed,zx⟩ := conditions c X hx
      simpa using And.intro sub (And.intro sz (And.intro closed zx))
    have b := count_through_pair (F.invol c) (F.moving c) U ∅ (fam c) 6 z valid
    simp only [sdiff_empty,card_empty,Nat.sub_zero] at b
    change (fam c).card ≤ (Inside F c U-1).choose 2 at b
    rw [key] at b
    exact (Nat.mul_le_mul_left m b).trans (choose_chord a i m im)
  have count := (card_le_card cover).trans card_biUnion_le
  have middle := sum_le_sum (s:=S) (fun c _ => per c)
  rw [← Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,← Finset.sum_mul] at middle
  have all := sum_le_sum_of_subset_of_nonneg (f:=fun c => Inside F c Uᶜ) (subset_univ S) (fun _ _ _ => Nat.zero_le _)
  rw [sum_inside F] at all
  change H.card≤chordBound g u
  apply (Nat.le_div_iff_mul_le den).mpr
  rw [Nat.mul_comm H.card]
  apply (Nat.mul_le_mul_left m count).trans
  apply middle.trans
  exact Nat.add_le_add (by simpa [Nat.mul_assoc] using Nat.mul_le_mul_right (m*low) sc)
    (Nat.mul_le_mul_right delta all)

theorem sides_local_improved (F : Factor A C) (B D U : Finset A) (s : Nat) (z : A) (zu : z∈U)
    (rain : Rainbow F B) (db : D⊆B) (ub : U⊆Bᶜ) :
    ((sides F D U s).filter (fun X => z∈X)).card ≤
      improvedDegree (Fintype.card C) Bᶜ.card B.card D.card s U.card := by
  have old := sides_local F B D U s z zu rain db ub
  have tot : Bᶜ.card+B.card-U.card=Uᶜ.card := by simp only [card_compl]; have := B.card_le_univ; omega
  unfold improvedDegree
  dsimp only
  split
  next cond =>
    refine Nat.le_min.mpr ⟨old,?_⟩
    obtain ⟨d,r,gu,den⟩ := cond
    obtain rfl := card_eq_zero.mp d
    subst s
    rw [tot] at gu den ⊢
    exact six_local F U z zu gu den
  next => exact old
end WildSieve
