import FrozenRows
namespace WildSieve
open Finset

def priced (r : Fin 3 → CutRow) (w : Fin 3 → Nat) (limit price : Nat) :=
  limit*price + ∑ i,(r i).colors * (w i-price)

def largestCosts (r : Fin 3 → CutRow) (w : Fin 3 → Nat) (limit : Nat) :=
  min (priced r w limit 0) (min (priced r w limit (w 0))
    (min (priced r w limit (w 1)) (priced r w limit (w 2))))

def totalFor (n N b d s u : Nat) :=
  let r := rowData n N b d
  ∑ i,(r i).colors * rowAll (r i) s u

def degreeFor (n N b d s u : Nat) :=
  let r := rowData n N b d
  if s≤u then min (totalFor n N b d s u)
    (largestCosts r (fun i => rowSpecial (r i) s u) d +
     largestCosts r (fun i => rowRegular (r i) s u) (u-1)) else 0

private theorem price_sum {C : Type} [DecidableEq C] (S : Finset C) (v : C → Nat)
    (classes : Fin 3 → Finset C) (r : Fin 3 → CutRow) (w : Fin 3 → Nat)
    (cover : ∀ c∈S,∃ i, c∈classes i ∧ v c ≤ w i)
    (sizes : ∀ i,(classes i).card = (r i).colors)
    (limit : Nat) (cap : S.card≤limit) (p : Nat) :
    ∑ c∈S,v c ≤ priced r w limit p := by
  classical
  have each (c) (hc : c∈S) : v c ≤ p + ∑ i : Fin 3, if c∈classes i then w i-p else 0 := by
    obtain ⟨i,inc,hv⟩ := cover c hc
    have single := Finset.single_le_sum (s := (univ : Finset (Fin 3)))
      (f := fun i => if c∈classes i then w i-p else 0) (fun i _ => Nat.zero_le _) (mem_univ i)
    simp only [if_pos inc] at single
    omega
  have tot (i : Fin 3) : (∑ c∈S, if c∈classes i then w i-p else 0) ≤ (r i).colors*(w i-p) := by
    rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,← sizes]
    exact Nat.mul_le_mul_right _ (card_le_card (fun _ hx => (mem_filter.mp hx).2))
  have h := sum_le_sum each
  rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,Finset.sum_comm] at h
  exact h.trans (Nat.add_le_add (Nat.mul_le_mul_right _ cap) (sum_le_sum (fun i _ => tot i)))

private theorem top_sum {C : Type} [DecidableEq C] (S : Finset C) (v : C → Nat)
    (classes : Fin 3 → Finset C) (r : Fin 3 → CutRow) (w : Fin 3 → Nat)
    (cover : ∀ c∈S,∃ i, c∈classes i ∧ v c ≤ w i)
    (sizes : ∀ i,(classes i).card = (r i).colors)
    (limit : Nat) (cap : S.card≤limit) :
    ∑ c∈S,v c ≤ largestCosts r w limit :=
  let h := price_sum S v classes r w cover sizes limit cap
  Nat.le_min.mpr ⟨h 0,Nat.le_min.mpr ⟨h _,Nat.le_min.mpr ⟨h _,h _⟩⟩⟩

variable {A C : Type} [LinearOrder A] [Fintype A] [Fintype C]

noncomputable def sides (F : Factor A C) (D U : Finset A) (s : Nat) :=
  univ.biUnion (fun c => candidates F c D U s)

omit [Fintype A] in
theorem side_mem {F : Factor A C} {D U X : Finset A} {s : Nat} :
    X ∈ sides F D U s ↔ ∃ c,X ∈ candidates F c D U s := by
  simp [sides]

private theorem total_family (F : Factor A C) (B D U : Finset A) (s : Nat)
    (rain : Rainbow F B) (db : D⊆B) (ub : U⊆Bᶜ)
    (family : C → Finset (Finset A)) (ok : ∀ c,family c ⊆ candidates F c D U s)
    (S : Finset C) (ne : ∀ c∈S,(family c).Nonempty) :
    ∑ c∈S,(family c).card ≤ totalFor (Fintype.card C) Bᶜ.card B.card D.card s U.card := by
  classical
  let r := rowData (Fintype.card C) Bᶜ.card B.card D.card
  have cover (c) (hc : c∈S) : ∃ i,c∈classColors F B D i ∧ (family c).card≤rowAll (r i) s U.card := by
    obtain ⟨i,inc,total,_⟩ := per_color F c B D U s _ rain db ub (ne c hc) (ok c)
    exact ⟨i,inc,total⟩
  have h := price_sum S (fun c => (family c).card) _ r _ cover (color_classes F B D rain db)
    S.card (le_refl _) 0
  simpa [priced,totalFor,r] using h

theorem sides_total (F : Factor A C) (B D U : Finset A) (s : Nat)
    (rain : Rainbow F B) (db : D⊆B) (ub : U⊆Bᶜ) :
    (sides F D U s).card ≤ totalFor (Fintype.card C) Bᶜ.card B.card D.card s U.card := by
  classical
  let fam c := candidates F c D U s
  let S := univ.filter (fun c => (fam c).Nonempty)
  have sub : sides F D U s ⊆ S.biUnion fam := by
    intro X hx
    obtain ⟨c,hc⟩ := side_mem.mp hx
    exact mem_biUnion.mpr ⟨c,mem_filter.mpr ⟨mem_univ _,X,hc⟩,hc⟩
  exact (card_le_card sub).trans (card_biUnion_le.trans
    (total_family F B D U s rain db ub fam (fun _ => Subset.rfl) S (fun _ h => (mem_filter.mp h).2)))

theorem sides_local (F : Factor A C) (B D U : Finset A) (s : Nat) (z : A) (zu : z∈U)
    (rain : Rainbow F B) (db : D⊆B) (ub : U⊆Bᶜ) :
    ((sides F D U s).filter (fun X => z∈X)).card ≤
      degreeFor (Fintype.card C) Bᶜ.card B.card D.card s U.card := by
  classical
  let H := (sides F D U s).filter (fun X => z∈X)
  by_cases em : H=∅
  · change H.card ≤ _
    simp [em]
  obtain ⟨X0,x0⟩ := nonempty_iff_ne_empty.mpr em
  obtain ⟨c0,h0⟩ := side_mem.mp (mem_filter.mp x0).1
  have small : s≤U.card := (candidate_mem.mp h0).2.1 ▸ card_le_card (candidate_mem.mp h0).1
  simp only [degreeFor,if_pos small]
  apply Nat.le_min.mpr
  refine ⟨(card_le_card (filter_subset _ _)).trans (sides_total F B D U s rain db ub),?_⟩
  let r := rowData (Fintype.card C) Bᶜ.card B.card D.card
  let fam c := (candidates F c D U s).filter (fun X => z∈X)
  let P := univ.filter (fun c => (fam c).Nonempty ∧ z∈forced (F.f c) B D)
  let Q := univ.filter (fun c => (fam c).Nonempty ∧ z∉forced (F.f c) B D)
  have cover : H ⊆ P.biUnion fam ∪ Q.biUnion fam := by
    intro X hx
    obtain ⟨side,zx⟩ := mem_filter.mp hx
    obtain ⟨c,hc⟩ := side_mem.mp side
    have member : X∈fam c := mem_filter.mpr ⟨hc,zx⟩
    by_cases has : z∈forced (F.f c) B D
    · exact mem_union_left _ (mem_biUnion.mpr ⟨c,mem_filter.mpr ⟨mem_univ _,⟨X,member⟩,has⟩,member⟩)
    · exact mem_union_right _ (mem_biUnion.mpr ⟨c,mem_filter.mpr ⟨mem_univ _,⟨X,member⟩,has⟩,member⟩)
  have per (c) (ne : (fam c).Nonempty) :=
    per_color F c B D U s (fam c) rain db ub ne (filter_subset _ _)
  have pc (c) (hc : c∈P) : ∃ i,c∈classColors F B D i ∧ (fam c).card ≤ rowSpecial (r i) s U.card := by
    obtain ⟨ne,has⟩ := (mem_filter.mp hc).2
    obtain ⟨i,inc,_,pr⟩ := per c ne
    exact ⟨i,inc,(pr z (fun _ h => (mem_filter.mp h).2)).1 has⟩
  have qc (c) (hc : c∈Q) :
      F.f c z∈U ∧ ∃ i,c∈classColors F B D i ∧ (fam c).card ≤ rowRegular (r i) s U.card := by
    obtain ⟨ne,no⟩ := (mem_filter.mp hc).2
    obtain ⟨i,inc,_,pr⟩ := per c ne
    obtain ⟨fu,bound⟩ := (pr z (fun _ h => (mem_filter.mp h).2)).2 no
    exact ⟨fu,i,inc,bound⟩
  have np : P.card ≤ D.card := by
    apply card_le_card_of_injOn (fun c => F.f c z) _ (F.unique z).injOn
    intro c hc
    obtain ⟨y,yd,fy⟩ := mem_image.mp (mem_sdiff.mp (mem_filter.mp hc).2.2).1
    simpa only [← fy,F.invol c y] using yd
  have nq : Q.card ≤ U.card-1 := by
    rw [← card_erase_of_mem zu]
    exact card_le_card_of_injOn (fun c => F.f c z)
      (fun c hc => mem_erase.mpr ⟨(F.moving c z).symm,(qc c hc).1⟩) (F.unique z).injOn
  have capP := top_sum P (fun c => (fam c).card) _ r _ pc (color_classes F B D rain db) _ np
  have capQ := top_sum Q (fun c => (fam c).card) _ r _ (fun c hc => (qc c hc).2)
    (color_classes F B D rain db) _ nq
  exact (card_le_card cover).trans ((card_union_le _ _).trans (Nat.add_le_add
    (card_biUnion_le.trans capP) (card_biUnion_le.trans capQ)))
end WildSieve
