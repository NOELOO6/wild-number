import TrimmedScopes
namespace WildSieve
open Finset

def survivingWays (d j : Nat) :=
  if d=1 ∧ j=3 then 240 else if d=0 ∧ j=4 then 15300 else ways j

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
  unfold survivingWays
  split
  next h =>
    obtain ⟨one,rfl⟩ := h
    have isRoot : D={root} := by
      by_cases add : 0<f ∧ 2*3<t
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
    exact root_nine F B root f t hr X (isRoot ▸ hit)
  next =>
    split
    next h =>
      obtain ⟨zero,rfl⟩ := h
      exact empty_twelve F B root f t X (card_eq_zero.mp zero ▸ hit)
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

theorem frozen_trimmed (F : Factor A C) (B : Finset A) (root : A) (f t : Nat)
    (hr : root∈B) (bs : B.card=f+1) (ws : Bᶜ.card=3*t) (rain : Rainbow F B) (shape : f=0 ∨ 2≤f)
    (h : Nat → ℚ) (cert : TrimCert (Fintype.card C) f t h) :
    ∃ L : Layout (univ : Finset (Free B)), ∀ j ∈ shortLevels ∪ longLevels t, ∀ X ∈ badScopes F B root f t j,
      L ∉ sealEvent X := by
  classical
  let bad := badScopes F B root f t
  refine trimmed_partition t ((Fintype.card_coe Bᶜ).trans ws) shortLevels (longLevels t) bad ?_ ?_
    (degBound (Fintype.card C) f t) (fun U z zu j _ => bad_scope_degree F B root f t hr bs ws rain U z zu j)
    h cert.1 cert.2.1 ?_
  · intro j _ X hx
    obtain ⟨D,_,hx⟩ := (mem_gather _ _ X).mp hx
    exact (pull_mem.mp hx).1
  · intro j hj
    simp [shortLevels] at hj
    omega
  · apply lt_of_le_of_lt _ cert.2.2
    apply sum_le_sum
    intro j _
    rw [←sum_mul]
    apply mul_le_mul_of_nonneg_right
    · exact_mod_cast bounded_subdivisions F B root f t j hr bs ws rain shape
    · exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (cert.1 _ (Nat.sub_le _ _)).le
end WildSieve
