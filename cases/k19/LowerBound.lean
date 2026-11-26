import EdgeWalk
namespace WildLower
open EdgeWalk WildDeletion
abbrev V := Fin 19
abbrev Edges := List (Edge 19)
def vertices := List.finRange 19
def touches (v : V) (e : Edge 19) := v == e.1 || v == e.2
def degree (w : Edges) (v : V) := (w.filter (touches v)).length

private theorem inside {E : V → V → Prop} {a b : V} (set : V → Prop) (ha : set a)
    (closed : ∀ u v, set u → E u v → set v) (h : Walk E a b) : set b := by
  induction h with
  | stay => exact ha
  | step _ e ih => exact closed _ _ ih e

private theorem split_edge (w m : Edges) {u v} (h : Adj (w++m) u v) : Adj w u v ∨ Adj m u v := by
  rcases h with h | h <;> rcases List.mem_append.mp h with t | t
  · exact Or.inl (Or.inl t)
  · exact Or.inr (Or.inl t)
  · exact Or.inl (Or.inr t)
  · exact Or.inr (Or.inr t)

private theorem one_member {α} {xs : List α} (h : xs.length = 1) {a b} (ha : a ∈ xs) (hb : b ∈ xs) :
    a = b := by
  cases xs with
  | nil => contradiction
  | cons x xs =>
    cases xs with
    | nil => simp at ha hb; exact ha.trans hb.symm
    | cons y ys => simp at h

private theorem neighbor_only {w : Edges} {a b u : V} (he : (a,b) ∈ w)
    (hd : degree w a = 1) (hu : Adj w a u) : u = b := by
  have m : (a,b) ∈ w.filter (touches a) := List.mem_filter.mpr ⟨he,by simp [touches]⟩
  rcases hu with h | h
  · have h' : (a,u) ∈ w.filter (touches a) := List.mem_filter.mpr ⟨h,by simp [touches]⟩
    exact congrArg Prod.snd (one_member hd h' m)
  · have h' : (u,a) ∈ w.filter (touches a) := List.mem_filter.mpr ⟨h,by simp [touches]⟩
    have eq := one_member hd h' m
    have e1 := congrArg Prod.fst eq
    have e2 := congrArg Prod.snd eq
    exact e1.trans e2
private theorem neighbor_only_right {w : Edges} {a b u : V} (he : (a,b) ∈ w)
    (hd : degree w b = 1) (hu : Adj w b u) : u = a := by
  have m : (a,b) ∈ w.filter (touches b) := List.mem_filter.mpr ⟨he,by simp [touches]⟩
  rcases hu with h | h
  · have h' : (b,u) ∈ w.filter (touches b) := List.mem_filter.mpr ⟨h,by simp [touches]⟩
    have eq := one_member hd h' m
    exact (congrArg Prod.snd eq).trans (congrArg Prod.fst eq)
  · have h' : (u,b) ∈ w.filter (touches b) := List.mem_filter.mpr ⟨h,by simp [touches]⟩
    exact congrArg Prod.fst (one_member hd h' m)

/-- The hypotheses are precisely the missing color at each point, the
matching property of each color, and an edge color for each pair. -/
structure Coloring (C : Type) where
  edges : C → Edges
  missing : ∀ a, ∃ c, ∀ b, ¬ Adj (edges c) a b
  proper : ∀ c a b d, Adj (edges c) a b → Adj (edges c) a d → b = d
  complete : ∀ a b, a ≠ b → ∃ c, Adj (edges c) a b

private theorem degrees_positive {C} (g : Coloring C) (w : Edges)
    (paths : ∀ c, Connected (Adj (w++g.edges c))) (a : V) : 0 < degree w a := by
  obtain ⟨c,absent⟩ := g.missing a
  have other : ∀ a : V, ∃ b : V, b ≠ a := by
    intro x
    by_cases h : x = 0
    · exact ⟨1,by rw [h]; decide⟩
    · exact ⟨0,Ne.symm h⟩
  obtain ⟨b,ne⟩ := other a
  apply Classical.byContradiction
  intro no
  have z : (w.filter (touches a)).length = 0 := Nat.eq_zero_of_not_pos no
  have empty := List.length_eq_zero_iff.mp z
  have closed (u v : V) (hu : u = a) (e : Adj (w++g.edges c) u v) : v = a := by
    subst u
    rcases split_edge _ _ e with ew | ec
    · rcases ew with h | h
      · have hm : (a,v) ∈ w.filter (touches a) := List.mem_filter.mpr ⟨h,by simp [touches]⟩
        rw [empty] at hm; contradiction
      · have hm : (v,a) ∈ w.filter (touches a) := List.mem_filter.mpr ⟨h,by simp [touches]⟩
        rw [empty] at hm; contradiction
    · exact False.elim (absent v ec)
  exact ne (inside (· = a) rfl closed (paths c a b))

private theorem no_two_leaves {C} (g : Coloring C) (w : Edges)
    (paths : ∀ c, Connected (Adj (w++g.edges c))) {a b : V} (ab : a ≠ b) (he : (a,b) ∈ w)
    (ha : degree w a = 1) (hb : degree w b = 1) : False := by
  obtain ⟨c,col⟩ := g.complete a b ab
  have other : ∀ a b : V, ∃ t : V, t ≠ a ∧ t ≠ b := by
    intro x y
    by_cases x0 : x = 0 <;> by_cases y0 : y = 0
    · exact ⟨1,by rw [x0,y0]; decide⟩
    · by_cases y1 : y = 1
      · exact ⟨2,by rw [x0,y1]; decide⟩
      · exact ⟨1,by rw [x0]; decide,Ne.symm y1⟩
    · by_cases x1 : x = 1
      · exact ⟨2,by rw [x1,y0]; decide⟩
      · exact ⟨1,Ne.symm x1,by rw [y0]; decide⟩
    · exact ⟨0,Ne.symm x0,Ne.symm y0⟩
  obtain ⟨t,hta,htb⟩ := other a b
  have closed (u v : V) (hu : u = a ∨ u = b) (e : Adj (w++g.edges c) u v) : v = a ∨ v = b := by
    rcases hu with rfl | rfl <;> rcases split_edge _ _ e with ew | ec
    · exact Or.inr (neighbor_only he ha ew)
    · exact Or.inr (g.proper _ _ _ _ ec col)
    · exact Or.inl (neighbor_only_right he hb ew)
    · exact Or.inl (g.proper _ _ _ _ ec col.symm)
  exact (inside (fun v => v = a ∨ v = b) (Or.inl rfl) closed (paths c a t)).elim hta htb

def sumOn {α : Type} (xs : List α) (f : α → Nat) := (xs.map f).sum
private theorem plus {α} (xs : List α) (f g : α → Nat) :
    sumOn xs (fun x => f x + g x) = sumOn xs f + sumOn xs g := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [sumOn,List.map_cons,List.sum_cons] at ih ⊢; omega

def load (w : Edges) (v : V) := if degree w v = 1 then 2 else 1
def pay (w : Edges) (e : Edge 19) (v : V) := if touches v e then load w v else 0

private theorem account (w es : Edges) (v : V) :
    sumOn es (fun e => pay w e v) = (es.filter (touches v)).length * load w v := by
  induction es with
  | nil => simp [sumOn]
  | cons e es ih => cases hp : touches v e <;>
      simp [sumOn,pay,hp,List.filter_cons,Nat.succ_mul] at ih ⊢ <;> omega

private theorem swap (w es : Edges) :
    sumOn vertices (fun v => sumOn es (fun e => pay w e v)) =
      sumOn es (fun e => sumOn vertices (pay w e)) := by
  induction es with
  | nil => change sumOn vertices (fun _ => 0) = 0; decide
  | cons e es ih =>
    change sumOn vertices (fun v => pay w e v + sumOn es (fun t => pay w t v)) = _
    rw [plus,ih]; rfl

private theorem per_edge (w : Edges) (a b : V) (ab : a ≠ b) :
    sumOn vertices (pay w (a,b)) = load w a + load w b := by
  have split (v : V) : pay w (a,b) v =
      (if v = a then load w a else 0)+(if v = b then load w b else 0) := by
    by_cases x : v = a <;> by_cases y : v = b <;> simp_all [pay,touches]
  rw [show pay w (a,b) = _ from funext split,plus]
  have atom (x : V) (z : Nat) : sumOn vertices (fun v => if v=x then z else 0) = z := by
    have only : ∀ x : V, ((vertices.filter (· == x)).length) = 1 := by decide
    have count (ls : List V) : sumOn ls (fun v => if v=x then z else 0) = (ls.filter (· == x)).length*z := by
      induction ls with
      | nil => simp [sumOn]
      | cons v ls ih =>
        by_cases h : v = x <;> simp [sumOn,h,List.filter_cons,Nat.succ_mul] at ih ⊢ <;> omega
    rw [count,only,Nat.one_mul]
  rw [atom,atom]

private theorem minSum {α} (xs : List α) (f : α → Nat) (k : Nat) (h : ∀ x ∈ xs, k ≤ f x) :
    k*xs.length ≤ sumOn xs f := by
  induction xs with
  | nil => simp [sumOn]
  | cons x xs ih =>
    have a := h x (by simp); have b := ih (fun y hy => h y (by simp [hy]))
    simp only [List.length_cons,Nat.mul_succ,sumOn,List.map_cons,List.sum_cons] at b ⊢; omega
private theorem maxSum {α} (xs : List α) (f : α → Nat) (k : Nat) (h : ∀ x ∈ xs, f x ≤ k) :
    sumOn xs f ≤ k*xs.length := by
  induction xs with
  | nil => simp [sumOn]
  | cons x xs ih =>
    have a := h x (by simp); have b := ih (fun y hy => h y (by simp [hy]))
    simp only [List.length_cons,Nat.mul_succ,sumOn,List.map_cons,List.sum_cons] at b ⊢; omega

theorem thirteen_necessary {C} (g : Coloring C) (w : Edges) (lines : ∀ e ∈ w, e.1 ≠ e.2)
    (paths : ∀ c, Connected (Adj (w++g.edges c))) : 13 ≤ w.length := by
  have lo := minSum vertices (fun v => sumOn w (fun e => pay w e v)) 2 (by
    intro v _
    change 2 ≤ sumOn w (fun e => pay w e v)
    rw [account]
    change 2 ≤ degree w v * load w v
    have pos := degrees_positive g w paths v
    unfold load
    split <;> omega)
  have hi := maxSum w (fun e => sumOn vertices (pay w e)) 3 (by
    intro ⟨a,b⟩ he
    have ne := lines (a,b) he
    change sumOn vertices (pay w (a,b)) ≤ 3
    rw [per_edge w a b ne]
    by_cases ha : degree w a = 1 <;> by_cases hb : degree w b = 1
    · exact False.elim (no_two_leaves g w paths ne he ha hb)
    all_goals simp [load,ha,hb])
  rw [swap] at lo
  have n : vertices.length = 19 := by decide
  rw [n] at lo
  omega
#print axioms thirteen_necessary
end WildLower
