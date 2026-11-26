import Delete

/- Ten arbitrary wild edges on sixteen points leave a point untouched in
   any successful coloring. The proof counts incidences and excludes an
   isolated wild pair by the color of its own edge. -/
namespace Untouched16
open WildDeletion
abbrev V := Fin 16
abbrev Edge := V × V
def vertices : List V := List.finRange 16
def total {α : Type} (xs : List α) (f : α → Nat) : Nat := (xs.map f).sum
theorem total_nil {α : Type} (f : α → Nat) : total [] f = 0 := rfl
theorem total_cons {α : Type} (a : α) (as : List α) (f : α → Nat) :
    total (a::as) f = f a + total as f := rfl

theorem total_add {α : Type} (xs : List α) (f g : α → Nat) :
    total xs (fun x => f x + g x) = total xs f + total xs g := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [total_cons, ih]; omega

theorem total_zero {α : Type} (xs : List α) : total xs (fun _ => 0) = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa only [total_cons, Nat.zero_add] using ih

theorem transpose {α β : Type} (xs : List α) (ys : List β) (f : α → β → Nat) :
    total xs (fun x => total ys (f x)) = total ys (fun y => total xs (fun x => f x y)) := by
  induction xs with
  | nil => exact (total_zero ys).symm
  | cons x xs ih =>
    simp only [total_cons, total_add, ih]

theorem constant_total {α : Type} (xs : List α) (f : α → Nat) (k : Nat)
    (h : ∀ x ∈ xs, f x = k) : total xs f = xs.length * k := by
  induction xs with
  | nil => simp [total]
  | cons x xs ih =>
    rw [total_cons, h x (by simp), ih (by intro z hz; exact h z (by simp [hz]))]
    simp [Nat.add_mul, Nat.add_comm]

theorem total_mono {α : Type} (xs : List α) (f g : α → Nat)
    (h : ∀ a ∈ xs, f a ≤ g a) : total xs f ≤ total xs g := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (by intro y hy; exact h y (by simp [hy]))
    simp only [total_cons]; omega

def inc (e : Edge) (x : V) : Nat := if x = e.1 ∨ x = e.2 then 1 else 0
def deg (es : List Edge) (x : V) := total es (fun e => inc e x)
def heavy (es : List Edge) (x : V) := if 2 ≤ deg es x then deg es x else 0

theorem full_vertices : ∀ x : V, x ∈ vertices := by decide
theorem size_vertices : vertices.length = 16 := by decide
theorem incidences : ∀ a b : V, a ≠ b → total vertices (inc (a,b)) = 2 := by decide
theorem degree_sum (es : List Edge) (proper : ∀ e ∈ es, e.1 ≠ e.2) :
    total vertices (deg es) = es.length*2 := by
  change total vertices (fun x => total es (fun e => inc e x)) = _
  rw [← transpose es vertices inc]
  exact constant_total _ _ _ (fun e he => incidences e.1 e.2 (proper e he))

theorem term_le {α : Type} {xs : List α} (f : α → Nat) {x : α} (h : x ∈ xs) :
    f x ≤ total xs f := by
  induction xs with
  | nil => simp at h
  | cons a xs ih =>
    rw [total_cons]
    rcases List.mem_cons.mp h with rfl | hx
    · omega
    · have hh := ih hx; omega

theorem unique_small {α : Type} (f : α → Nat) {xs : List α} {x y : α}
    (hx : x ∈ xs) (hy : y ∈ xs) (fx : 0 < f x) (fy : 0 < f y)
    (small : total xs f ≤ 1) : x = y := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
    rw [total_cons] at small
    rcases List.mem_cons.mp hx with ha | hxT
    · rcases List.mem_cons.mp hy with hb | hyT
      · exact ha.trans hb.symm
      · have hh := term_le (xs := xs) f hyT; rw [ha] at fx; omega
    · rcases List.mem_cons.mp hy with hb | hyT
      · have hh := term_le (xs := xs) f hxT; rw [hb] at fy; omega
      · exact ih hxT hyT (by omega)

def adjWild (es : List Edge) (x y : V) : Prop := (x,y) ∈ es ∨ (y,x) ∈ es
def full {C : Type} (mate : C → V → V) (es : List Edge) (c : C) (x y : V) : Prop :=
  mate c x = y ∨ adjWild es x y

theorem must_touch_heavy {C : Type} (mate : C → V → V) (es : List Edge)
    (inverse : ∀ c x, mate c (mate c x) = x)
    (allPairs : ∀ a b, a ≠ b → ∃ c, mate c a = b)
    (proper : ∀ e ∈ es, e.1 ≠ e.2) (good : ∀ c, Connected (full mate es c))
    (e : Edge) (he : e ∈ es) : 2 ≤ deg es e.1 ∨ 2 ≤ deg es e.2 := by
  apply Classical.byContradiction
  intro h
  have ha : deg es e.1 ≤ 1 := by omega
  have hb : deg es e.2 ≤ 1 := by omega
  obtain ⟨c,cm⟩ := allPairs _ _ (proper e he)
  have cm' : mate c e.2 = e.1 := by rw [← cm, inverse]
  let inPair : V → Prop := fun x => x = e.1 ∨ x = e.2
  have stays {x y : V} (inside : inPair x) (edge : full mate es c x y) : inPair y := by
    rcases edge with matchEdge | wild
    · rcases inside with rfl | rfl
      · exact Or.inr (matchEdge.symm.trans cm)
      · exact Or.inl (matchEdge.symm.trans cm')
    · have pin : inc e x = 1 := if_pos inside
      have d : deg es x ≤ 1 := inside.elim (fun h => h ▸ ha) (fun h => h ▸ hb)
      rcases wild with xy | yx
      · have eq := unique_small (fun k => inc k x) he xy (show 0 < inc e x from pin.symm ▸ Nat.zero_lt_one) (by simp [inc]) d
        exact Or.inr (congrArg Prod.snd eq).symm
      · have eq := unique_small (fun k => inc k x) he yx (show 0 < inc e x from pin.symm ▸ Nat.zero_lt_one) (by simp [inc]) d
        exact Or.inl (congrArg Prod.fst eq).symm
  have noleave {x y : V} (w : Walk (full mate es c) x y) : inPair x → inPair y := by
    induction w with
    | stay => exact id
    | step _ edge ih => exact fun hx => stays (ih hx) edge
  have extOK : ∀ a b : V, vertices.any (fun v => decide (v ≠ a ∧ v ≠ b)) = true := by decide
  obtain ⟨z,_,hzz⟩ := List.any_eq_true.mp (extOK e.1 e.2)
  obtain ⟨za,zb⟩ := of_decide_eq_true hzz
  exact (noleave (good c e.1 z) (Or.inl rfl)).elim za zb

theorem untouched {C : Type} (mate : C → V → V) (es : List Edge)
    (inverse : ∀ c x, mate c (mate c x) = x)
    (allPairs : ∀ a b, a ≠ b → ∃ c, mate c a = b)
    (proper : ∀ e ∈ es, e.1 ≠ e.2) (ten : es.length ≤ 10)
    (good : ∀ c, Connected (full mate es c)) :
    ∃ r : V, deg es r = 0 := by
  apply Classical.byContradiction
  intro none
  have pos (x : V) : 0 < deg es x := Nat.pos_of_ne_zero (fun hz => none ⟨x,hz⟩)
  let weight := fun (e : Edge) (x : V) => if 2 ≤ deg es x then inc e x else 0
  have fromEdge (e : Edge) (he : e ∈ es) : 1 ≤ total vertices (weight e) := by
    rcases must_touch_heavy mate es inverse allPairs proper good e he with h | h
    · have ht := term_le (weight e) (full_vertices e.1)
      simpa [weight,h,inc] using ht
    · have ht := term_le (weight e) (full_vertices e.2)
      simpa [weight,h,inc] using ht
  have fromVertex (x : V) : total es (fun e => weight e x) = heavy es x := by
    by_cases h : 2 ≤ deg es x
    · simp only [weight,h,if_true,heavy]; rfl
    · simp only [weight,h,if_false,heavy]; exact total_zero _
  have lower := total_mono es (fun _ => 1) (fun e => total vertices (weight e)) fromEdge
  rw [constant_total es _ 1 (fun _ _ => rfl), Nat.mul_one, transpose es vertices weight] at lower
  simp only [fromVertex] at lower
  have localBound (x : V) : heavy es x + 2 ≤ deg es x + deg es x := by
    have := pos x
    unfold heavy; split <;> omega
  have upper := total_mono vertices (fun x => heavy es x + 2) (fun x => deg es x + deg es x)
     (fun x _ => localBound x)
  rw [total_add, total_add, constant_total vertices _ 2 (fun _ _ => rfl), size_vertices,
      degree_sum es proper] at upper
  change es.length ≤ total vertices (heavy es) at lower
  omega

#print axioms untouched

abbrev Other (r : V) := {v : V // v ≠ r}
def induced (E : V → V → Prop) (r : V) (a b : Other r) := E a.val b.val

theorem delete_leaf (E : V → V → Prop) (r : V) (p : Other r)
    (out : ∀ x, E r x ↔ x = p.val) (into : ∀ x, E x r ↔ x = p.val) :
    Connected E ↔ Connected (induced E r) := by
  let shrink : V → Other r := fun x => if h : x = r then p else ⟨x,h⟩
  have orig (x : Other r) : shrink x.val = x := by simp [shrink,x.property]
  have sr : shrink r = p := by simp [shrink]
  constructor
  · intro big a b
    have maps (x y : V) (e : E x y) : Walk (induced E r) (shrink x) (shrink y) := by
      by_cases hx : x = r
      · subst x
        have hy := (out y).mp e
        rw [sr, hy, orig]; exact .stay _
      · by_cases hy : y = r
        · subst y
          have hh := (into x).mp e
          rw [sr, hh, orig]; exact .stay _
        · simp only [shrink,dif_neg hx,dif_neg hy]
          exact .step (.stay _) e
    simpa only [orig] using Walk.mapInto shrink maps (big a.val b.val)
  · intro small a b
    have old (x y : Other r) : Walk E x.val y.val :=
      Walk.mapInto Subtype.val (fun _ _ e => .step (.stay _) e) (small x y)
    have start : Walk E r p.val := .step (.stay _) ((out p.val).mpr rfl)
    have finish : Walk E p.val r := .step (.stay _) ((into p.val).mpr rfl)
    by_cases ha : a = r
    · subst a
      by_cases hb : b = r
      · subst b; exact .stay _
      · exact start.join (old p ⟨b,hb⟩)
    · by_cases hb : b = r
      · subst b; exact (old ⟨a,ha⟩ p).join finish
      · exact old ⟨a,ha⟩ ⟨b,hb⟩

theorem no_wild_at (es : List Edge) (r v : V) (hz : deg es r = 0) : ¬adjWild es r v := by
  intro hw
  rcases hw with e | e
  · have h := term_le (fun k => inc k r) e
    change inc (r,v) r ≤ deg es r at h
    simp [inc,hz] at h
  · have h := term_le (fun k => inc k r) e
    change inc (v,r) r ≤ deg es r at h
    simp [inc,hz] at h

theorem deletion_at_untouched {C : Type} (mate : C → V → V) (es : List Edge)
    (inverse : ∀ c x, mate c (mate c x) = x) (noFixed : ∀ c x, mate c x ≠ x)
    (r : V) (free : deg es r = 0) (c : C) :
    Connected (full mate es c) ↔ Connected (induced (full mate es c) r) := by
  apply delete_leaf _ r ⟨mate c r, noFixed c r⟩
  · intro x
    constructor
    · rintro (he | hw)
      · exact he.symm
      · exact False.elim (no_wild_at es r x free hw)
    · exact fun h => Or.inl h.symm
  · intro x
    constructor
    · rintro (he | hw)
      · exact (inverse c x).symm.trans (congrArg (mate c) he)
      · exact False.elim (no_wild_at es r x free (hw.elim Or.inr Or.inl))
    · intro h; rw [h]; exact Or.inl (inverse c r)

/-- A point can be chosen after seeing the wild set. This equivalence
    quantifies over arbitrary colorings and lists of at most ten edges. -/
theorem ten_iff_some_deletion {C : Type} (mate : C → V → V) (es : List Edge)
    (inverse : ∀ c x, mate c (mate c x) = x) (noFixed : ∀ c x, mate c x ≠ x)
    (allPairs : ∀ a b, a ≠ b → ∃ c, mate c a = b)
    (proper : ∀ e ∈ es, e.1 ≠ e.2) (ten : es.length ≤ 10) :
    (∀ c, Connected (full mate es c)) ↔
    ∃ r : V, deg es r = 0 ∧ ∀ c, Connected (induced (full mate es c) r) := by
  constructor
  · intro good
    obtain ⟨r,hr⟩ := untouched mate es inverse allPairs proper ten good
    exact ⟨r,hr,fun c => (deletion_at_untouched mate es inverse noFixed r hr c).mp (good c)⟩
  · rintro ⟨r,hr,h⟩ c
    exact (deletion_at_untouched mate es inverse noFixed r hr c).mpr (h c)

#print axioms ten_iff_some_deletion
end Untouched16
