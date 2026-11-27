import MatchingRegions
namespace WildSieve
open Finset

def survivingWays (d j : Nat) :=
  if d=1 ∧ j=3 then 240 else if 4≤j ∧ d≤1 then ways j-saving (d=1) (3*j/2) j else ways j

def trimmedCount (n f t j : Nat) := ((widths f t j).map
  (fun d => totalFor n (3*t) (f+1) d (3*j) (3*t)*survivingWays d j)).sum

def TrimCert (n f t : Nat) (h : Nat → ℚ) :=
  (∀ u ≤ 3*t,0<h u) ∧ (∀ u,0<u → u≤3*t →
    ∑ j ∈ shortLevels,(degBound n f t u j : ℚ)*(sealWeight t j*h (u-3*j)) ≤ h (u-1)-h u) ∧
  (∑ j ∈ longLevels t,(trimmedCount n f t j : ℚ)*((ways (t-j):ℚ)/ways t*h (3*t-3*j))) < h (3*t)

private theorem weight_gather {α β : Type} [DecidableEq β] (f : α → Finset β) (l : List α)
    (w : β → Nat) (q : α → Nat) (h : ∀ a∈l,∑ b∈f a,w b ≤ q a) :
    ∑ b∈gather f l,w b ≤ (l.map q).sum := by
  induction l with
  | nil => simp [gather]
  | cons a l ih =>
    have both := sum_union_inter (s₁:=f a) (s₂:=gather f l) (f:=w)
    apply (Nat.le_add_right (∑ x∈f a ∪ gather f l,w x) (∑ x∈f a ∩ gather f l,w x)).trans
    rw [both]
    exact Nat.add_le_add (h a (by simp)) (ih (fun x hx => h x (by simp [hx])))

variable {A C : Type} [LinearOrder A] [Fintype A] [Fintype C]

private theorem scope_weight (F : Factor A C) (B : Finset A) (root : A) (f t j : Nat)
    (hr : root∈B) (bs : B.card=f+1) (shape : f=0 ∨ 2≤f) (D : Finset A)
    (hd : D∈choices B root f t j) (X : Finset (Free B)) (hit : X∈pullSides F B D (3*j)) :
    (admissible shortLevels (badScopes F B root f t) X).card≤survivingWays D.card j := by
  classical
  have root_of_one (one : D.card=1) : D={root} := by
      by_cases add : 0<f ∧ 2*j<t
      · simp [choices,add] at hd
        rcases hd with rfl|rfl|rfl|rfl
        · simp at one
        · rfl
        · rw [card_erase_of_mem hr,bs] at one
          omega
        · omega
      · simp [choices,add] at hd
        rcases hd with rfl|rfl
        · simp at one
        · rfl
  unfold survivingWays
  split
  next h =>
    obtain ⟨one,rfl⟩ := h
    exact root_nine F B root f t hr X (root_of_one one ▸ hit)
  next =>
    split
    next h =>
      obtain ⟨lo,small⟩ := h
      rcases Nat.eq_zero_or_pos D.card with zero|pos
      · rw [zero]
        exact even_regions F B root f t j X (card_eq_zero.mp zero ▸ hit) lo
      · have one : D.card=1 := by omega
        rw [one]
        exact odd_regions F B root f t j hr X (root_of_one one ▸ hit) lo
    next =>
      exact (card_le_univ _).trans_eq (card_layout j X (pull_mem.mp hit).1)

theorem bounded_subdivisions (F : Factor A C) (B : Finset A) (root : A) (f t j : Nat)
    (hr : root∈B) (bs : B.card=f+1) (ws : Bᶜ.card=3*t) (rain : Rainbow F B)
    (shape : f=0 ∨ 2≤f) :
    (∑ X∈badScopes F B root f t j,(admissible shortLevels (badScopes F B root f t) X).card)
      ≤ trimmedCount (Fintype.card C) f t j := by
  classical
  let w (X) := (admissible shortLevels (badScopes F B root f t) X).card
  let ts (D : Finset A) := totalFor (Fintype.card C) Bᶜ.card B.card D.card (3*j) Bᶜ.card
  let L := choices B root f t j
  have b := weight_gather (fun D => pullSides F B D (3*j)) L w (fun D => ts D*survivingWays D.card j) (by
    intro D hd
    have one := sum_le_sum (s:=pullSides F B D (3*j)) (fun X hx => scope_weight F B root f t j hr bs shape D hd X hx)
    apply one.trans
    rw [sum_const,nsmul_eq_mul]
    exact Nat.mul_le_mul_right _ (pull_total F B D _ rain (choices_sub B root hr f t j D hd)))
  unfold trimmedCount
  rw [← width_eq B root hr f t j bs,List.map_map]
  simpa only [badScopes,L,w,ts,ws,bs,Function.comp_apply] using b

theorem frozen_trimmed_actual (F : Factor A C) (B : Finset A) (root : A) (f t : Nat)
    (hr : root∈B) (bs : B.card=f+1) (ws : Bᶜ.card=3*t) (rain : Rainbow F B) (shape : f=0 ∨ 2≤f)
    (h : Nat → ℚ) (positive : ∀ u≤3*t,0<h u)
    (budget : ∀ U z,z∈U →
      ∑ j∈shortLevels,((active (badScopes F B root f t j) U z).card:ℚ)*
        (sealWeight t j*h (U.card-3*j)) ≤ h (U.card-1)-h U.card)
    (tail : (∑ j∈longLevels t,(trimmedCount (Fintype.card C) f t j:ℚ)*
      ((ways (t-j):ℚ)/ways t*h (3*t-3*j))) < h (3*t)) :
    ∃ L : Layout (univ : Finset (Free B)), ∀ j ∈ shortLevels ∪ longLevels t, ∀ X ∈ badScopes F B root f t j,
      L ∉ sealEvent X := by
  classical
  let bad := badScopes F B root f t
  refine trimmed_actual t ((Fintype.card_coe Bᶜ).trans ws) shortLevels (longLevels t) bad ?_ ?_
    h positive budget ?_
  · intro j _ X hx
    obtain ⟨D,_,hx⟩ := (mem_gather _ _ X).mp hx
    exact (pull_mem.mp hx).1
  · intro j hj
    simp [shortLevels] at hj
    omega
  · apply lt_of_le_of_lt _ tail
    apply sum_le_sum
    intro j _
    rw [←sum_mul]
    apply mul_le_mul_of_nonneg_right
    · exact_mod_cast bounded_subdivisions F B root f t j hr bs ws rain shape
    · exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (positive _ (Nat.sub_le _ _)).le
theorem frozen_trimmed (F : Factor A C) (B : Finset A) (root : A) (f t : Nat)
    (hr : root∈B) (bs : B.card=f+1) (ws : Bᶜ.card=3*t) (rain : Rainbow F B) (shape : f=0 ∨ 2≤f)
    (h : Nat → ℚ) (cert : TrimCert (Fintype.card C) f t h) :
    ∃ L : Layout (univ : Finset (Free B)), ∀ j ∈ shortLevels ∪ longLevels t, ∀ X ∈ badScopes F B root f t j,
      L ∉ sealEvent X := by
  apply frozen_trimmed_actual F B root f t hr bs ws rain shape h cert.1 _ cert.2.2
  intro U z hz
  have le : U.card≤3*t := U.card_le_univ.trans_eq ((Fintype.card_coe Bᶜ).trans ws)
  apply le_trans _ (cert.2.1 U.card (card_pos.mpr ⟨z,hz⟩) le)
  apply sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast bad_scope_degree F B root f t hr bs ws rain U z hz j)
    (mul_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
      (cert.1 _ ((Nat.sub_le _ _).trans le)).le)
end WildSieve
