import Std

/- A finite lemma for the unrestricted K15 argument. Marks can repeat.
   Lean verifies the average over the entire four-triple partition catalogue. -/
namespace Near15
set_option maxHeartbeats 0
set_option maxRecDepth 100000

abbrev Split := List Nat

def weight (m : Nat) : Nat :=
  ((List.range 12).filter fun i => m.testBit i).length
def masks (k : Nat) : List Nat := (List.range 4096).filter (fun m => weight m == k)
def triples := masks 3
def sixes := masks 6

/-- Choose the block containing the least remaining point. -/
def partitions : Nat → Nat → List Split
  | 0, remaining => if remaining == 0 then [[]] else []
  | k+1, remaining =>
    if remaining == 0 then [] else
    let first := (List.range 12).find? (fun i => remaining.testBit i)
    match first with
    | none => []
    | some i => triples.flatMap fun t =>
      if t.testBit i && (remaining &&& t) == t then
        (partitions k (remaining ^^^ t)).map (fun rest => t :: rest)
      else []

def catalogue : List Split := partitions 4 4095

def genuine (p : Split) : Bool :=
  p.length == 4 && p.all (fun t => weight t == 3 && t < 4096) &&
  p.foldl (· ||| ·) 0 == 4095

/-- A cut is sealed by the split when all its blocks are on one side or the other. -/
def isUnion (cut : Nat) (p : Split) : Bool :=
  p.all fun t => (cut &&& t) == 0 || (cut &&& t) == t

def total {α : Type} (xs : List α) (f : α → Nat) : Nat := (xs.map f).sum
def hit (cut : Nat) (p : Split) : Nat := if isUnion cut p then 1 else 0

theorem genuine_catalogue : catalogue.all genuine = true := by native_decide
theorem catalogue_size : catalogue.length = 15400 := by native_decide
theorem triple_frequency : triples.all (fun t => total catalogue (hit t) == 280) = true := by
  native_decide
theorem six_frequency : sixes.all (fun t => total catalogue (hit t) == 100) = true := by
  native_decide

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

theorem two_each {α : Type} (xs : List α) (f : α → Nat) (h : ∀ x ∈ xs, 2 ≤ f x) :
    xs.length * 2 ≤ total xs f := by
  induction xs with
  | nil => simp [total]
  | cons x xs ih =>
    have h1 := h x (by simp)
    have h2 := ih (by intro z hz; exact h z (by simp [hz]))
    simp only [total_cons, List.length_cons]; omega

/-- Fully quantified over all marked triples and balanced cuts with the two
    size bounds. The resulting split really partitions the twelve points. -/
theorem exists_near_split (ts ss : List Nat)
    (members₃ : ∀ t ∈ ts, t ∈ triples) (members₆ : ∀ s ∈ ss, s ∈ sixes)
    (small₃ : ts.length ≤ 75) (small₆ : ss.length ≤ 96) :
    ∃ p ∈ catalogue, genuine p = true ∧
      total ts (fun t => hit t p) + total ss (fun s => hit s p) ≤ 1 := by
  let cost := fun p => total ts (fun t => hit t p) + total ss (fun s => hit s p)
  have ht : total ts (fun t => total catalogue (hit t)) = ts.length * 280 :=
    constant_total _ _ _ (by
      intro t h; exact beq_iff_eq.mp (List.all_eq_true.mp triple_frequency t (members₃ t h)))
  have hs : total ss (fun s => total catalogue (hit s)) = ss.length * 100 :=
    constant_total _ _ _ (by
      intro s h; exact beq_iff_eq.mp (List.all_eq_true.mp six_frequency s (members₆ s h)))
  have tot : total catalogue cost = ts.length * 280 + ss.length * 100 := by
    unfold cost
    rw [total_add, ← transpose ts catalogue hit, ← transpose ss catalogue hit, ht, hs]
  apply Classical.byContradiction
  intro h
  have allLarge : ∀ p ∈ catalogue, 2 ≤ cost p := by
    intro p hp
    by_cases hh : cost p ≤ 1
    · exact False.elim (h ⟨p, hp, List.all_eq_true.mp genuine_catalogue p hp, hh⟩)
    · omega
  have contra := two_each catalogue cost allLarge
  rw [catalogue_size, tot] at contra
  omega

#print axioms Near15.exists_near_split
end Near15
