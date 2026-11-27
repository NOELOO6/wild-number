import SlotCuts

namespace WildSlots
open WildDeletion WildExact
abbrev Three := Fin 3
abbrev Port := Three ⊕ Three

def cell (i j a b : Three) := (a=i ↔ b=j)

/-- For three points, every binary pattern is constant outside one index. -/
private theorem singleton_pattern : ∀ f : Three → Bool,∃ i : Three,
    ∀ a b : Three,(a=i ↔ b=i) → f a=f b := by decide

theorem three_cells {V C : Type} (E : C → V → V → Prop) (sym : ∀ c {x y},E c x y → E c y x)
    (u v : Three → V) (p : Equiv.Perm Three) :
    passes E u v (assign p) ↔ ∀ i,passes E u v (cell i (p i)) := by
  constructor
  · intro h i
    apply passes_mono _ h
    intro a b (ab : p a=b)
    subst b
    exact p.injective.eq_iff.symm
  · apply pass_from_tests E sym u v p
    intro f
    obtain ⟨i,hi⟩ := singleton_pattern f
    exact ⟨i,fun a b h => hi a (p.symm b) (by simpa [cell,Equiv.symm_apply_eq] using h)⟩

def port {V : Type} (u v : Three → V) : Port → V := Sum.elim u v
def isolated (i j : Three) : Port → Prop := Sum.elim (·=i) (·=j)

def visible {V C : Type} (E : C → V → V → Prop) (u v : Three → V) :=
  ∀ c x,∃ t,Walk (E c) x (port u v t)

/-- A board entry is allowed precisely when every color has a residual path
from this pair of terminals to one of the other four. -/
def allowed {V C : Type} (E : C → V → V → Prop) (u v : Three → V) (i j : Three) :=
  ∀ c,∃ s t,isolated i j s ∧ ¬isolated i j t ∧
    Walk (E c) (port u v s) (port u v t)

private theorem outside_index : ∀ i : Three,∃ l : Three,l≠i := by decide

private theorem terminal_route {V : Type} {E : V → V → Prop} (u v : Three → V)
    (i j : Three) (s t : Port) (same : isolated i j s ↔ isolated i j t) :
    Walk (extend E u v (cell i j)) (port u v s) (port u v t) := by
  obtain ⟨k,hk⟩ := outside_index i
  obtain ⟨l,hl⟩ := outside_index j
  have lr (a b) (ab : a=i ↔ b=j) : Walk (extend E u v (cell i j)) (u a) (v b) :=
    .step (.stay _) (Or.inr ⟨a,b,ab,Or.inl ⟨rfl,rfl⟩⟩)
  have rl (a b) (ab : a=i ↔ b=j) : Walk (extend E u v (cell i j)) (v b) (u a) :=
    .step (.stay _) (Or.inr ⟨a,b,ab,Or.inr ⟨rfl,rfl⟩⟩)
  cases s with
  | inl a =>
    cases t with
    | inl b =>
      change a=i ↔ b=i at same
      by_cases a1 : a=i
      · exact (lr a j (iff_of_true a1 rfl)).join (rl b j (iff_of_true (same.mp a1) rfl))
      · exact (lr a l (iff_of_false a1 hl)).join (rl b l (iff_of_false (a1 ∘ same.mpr) hl))
    | inr b => exact lr a b same
  | inr a =>
    cases t with
    | inl b => exact rl b a same.symm
    | inr b =>
      change a=j ↔ b=j at same
      by_cases a1 : a=j
      · exact (rl i a (iff_of_true rfl a1)).join (lr i b (iff_of_true rfl (same.mp a1)))
      · exact (rl k a (iff_of_false hk a1)).join (lr k b (iff_of_false hk (a1 ∘ same.mpr)))

private theorem visible_of_pass {V C : Type} {E : C → V → V → Prop} (sym : ∀ c {x y},E c x y → E c y x)
    {u v : Three → V} {T : Three → Three → Prop} (yes : passes E u v T) : visible E u v := by
  classical
  intro c x
  let seen (a : V) := ∃ t,Walk (E c) a (port u v t)
  have terminal (t : Port) : seen (port u v t) := ⟨t,.stay _⟩
  have stable (a b) (h : extend (E c) u v T a b) : seen a ↔ seen b := by
    rcases h with e|⟨i,j,_,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩
    · exact ⟨fun ⟨t,w⟩ => ⟨t,(Walk.step (.stay _) (sym c e)).join w⟩,
        fun ⟨t,w⟩ => ⟨t,(Walk.step (.stay _) e).join w⟩⟩
    · exact iff_of_true (terminal (.inl i)) (terminal (.inr j))
    · exact iff_of_true (terminal (.inr j)) (terminal (.inl i))
  have h := constant_on_walk (f:=fun a => decide (seen a))
    (fun a b e => decide_eq_decide.mpr (stable a b e)) (yes c (port u v (.inl 0)) x)
  exact of_decide_eq_true (h.symm.trans (decide_eq_true (terminal (.inl 0))))

theorem board_entry {V C : Type} (E : C → V → V → Prop) (sym : ∀ c {x y},E c x y → E c y x)
    (u v : Three → V) (i j : Three) :
    passes E u v (cell i j) ↔ visible E u v ∧ allowed E u v i j := by
  classical
  constructor
  · intro yes
    refine ⟨visible_of_pass sym yes,?_⟩
    intro c
    by_contra no
    let inside (a : V) := ∃ s,isolated i j s ∧ Walk (E c) (port u v s) a
    have term (t : Port) : inside (port u v t) ↔ isolated i j t := by
      constructor
      · rintro ⟨s,hs,w⟩
        by_contra ht
        exact no ⟨s,t,hs,ht,w⟩
      · intro ht
        exact ⟨t,ht,.stay _⟩
    have step (a b) (h : extend (E c) u v (cell i j) a b) : inside a ↔ inside b := by
      rcases h with e|⟨l,r,ok,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩
      · constructor
        · rintro ⟨s,hs,w⟩
          exact ⟨s,hs,.step w e⟩
        · rintro ⟨s,hs,w⟩
          exact ⟨s,hs,.step w (sym c e)⟩
      · exact (term (.inl l)).trans (ok.trans (term (.inr r)).symm)
      · exact (term (.inr r)).trans (ok.symm.trans (term (.inl l)).symm)
    obtain ⟨k,hk⟩ := outside_index i
    have eq := constant_on_walk (f:=fun a => decide (inside a))
      (fun a b e => decide_eq_decide.mpr (step a b e)) (yes c (u i) (u k))
    exact hk ((term (.inl k)).mp ((decide_eq_decide.mp eq).mp ((term (.inl i)).mpr rfl)))
  · rintro ⟨reach,cross⟩ c x y
    let F := extend (E c) u v (cell i j)
    have lift {a b} (h : Walk (E c) a b) : Walk F a b :=
      Walk.mapInto (E:=E c) (F:=F) id (fun _ _ e => .step (.stay _) (Or.inl e)) h
    obtain ⟨s,t,hs,ht,bridge⟩ := cross c
    have from_s (a : Port) : Walk F (port u v s) (port u v a) := by
      by_cases ha : isolated i j a
      · exact terminal_route u v i j _ _ (iff_of_true hs ha)
      · exact (lift bridge).join (terminal_route u v i j _ _ (iff_of_false ht ha))
    obtain ⟨a,ax⟩ := reach c x
    obtain ⟨b,by'⟩ := reach c y
    have reverse {l m} (q : Walk F l m) := backwards (R:=F) (fun h => extend_symm (fun e => sym c e) h) q
    exact (((lift ax).join (reverse (from_s a))).join (from_s b)).join (reverse (lift by'))

/-- A valid placement of the three points is exactly a matching on the board.
The residual graph and its board can be computed once for all six placements. -/
theorem assignment_rule {V C : Type} (E : C → V → V → Prop) (sym : ∀ c {x y},E c x y → E c y x)
    (u v : Three → V) (p : Equiv.Perm Three) :
    passes E u v (assign p) ↔ visible E u v ∧ ∀ i,allowed E u v i (p i) := by
  rw [three_cells E sym]
  constructor
  · intro h
    exact ⟨((board_entry E sym u v _ _).mp (h 0)).1,fun i => ((board_entry E sym u v _ _).mp (h i)).2⟩
  · rintro ⟨vis,ok⟩ i
    exact (board_entry E sym u v _ _).mpr ⟨vis,ok i⟩

#print axioms assignment_rule
end WildSlots
