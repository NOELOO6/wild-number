import Teams

/- Count seven-point subsets in which no color can fit three whole pairs.
   The calculation below works for arbitrary lists of eight pair masks with
   one member containing point zero. Disjoint pair masks in a perfect
   matching ensure that every union of three pairs has six points. -/
namespace SevenSet
open Teams
set_option maxHeartbeats 0
set_option maxRecDepth 100000
structure Pick where
  i : Nat
  j : Nat
  k : Nat
deriving DecidableEq

def picks := (List.range 8).flatMap (fun k => (List.range k).flatMap
  (fun j => (List.range j).map (fun i => Pick.mk i j k)))
def weight (s : Nat) := ((List.range 16).filter s.testBit).length
def sets (rooted : Bool) := (List.range 65536).filter
  (fun s => weight s == 7 && (!rooted || s.testBit 0))
def capacity (rooted hasRoot : Bool) := if rooted && !hasRoot then 1 else 10
def side (m : Nat → Nat) (p : Pick) := m p.i ||| m p.j ||| m p.k
def contains (s z : Nat) : Nat := if (s &&& z) == s then 1 else 0
def six (s : Nat) := s < 65536 && weight s == 6
def incidence (m : Nat → Nat) (p : Pick) (z : Nat) :=
  if six (side m p) then contains (side m p) z else 0
def has (p : Pick) (r : Nat) := p.i == r || p.j == r || p.k == r
def misses (m : Nat → Nat) (z : Nat) := total picks (fun p => incidence m p z)
def cap (b : Bool) := if b then 245 else 560
def lower (b : Bool) := if b then 1330 else 3040

theorem sizes (b : Bool) : (sets b).length = if b then 5005 else 11440 := by
  cases b <;> native_decide
theorem small_indices : picks.all (fun p => p.i < 8 && p.j < 8 && p.k < 8) = true := by decide
theorem budgets (b : Bool) : (List.range 8).all (fun r =>
    total picks (fun p => capacity b (has p r)) == cap b) = true := by
  cases b <;> decide
theorem supersets (b : Bool) : (List.range 65536).all (fun s => !six s ||
    total (sets b) (contains s) == capacity b (s.testBit 0)) = true := by
  cases b <;> native_decide

theorem one_pick (b : Bool) (m : Nat → Nat) (r : Nat)
    (one : ∀ i < 8, (m i).testBit 0 = (i == r)) (p : Pick) (hp : p ∈ picks) :
    total (sets b) (incidence m p) ≤ capacity b (has p r) := by
  have bounds := List.all_eq_true.mp small_indices p hp
  simp at bounds
  have mark : (side m p).testBit 0 = has p r := by
    simp only [side, Nat.testBit_or, has]
    rw [one p.i bounds.1.1, one p.j bounds.1.2, one p.k bounds.2]
  by_cases yes : six (side m p) = true
  · have inRange : side m p < 65536 := by
      have also := yes
      simp only [six, Bool.and_eq_true, decide_eq_true_eq] at also
      exact also.1
    have h := List.all_eq_true.mp (supersets b) _ (List.mem_range.mpr inRange)
    rw [yes] at h
    have exactCount : total (sets b) (contains (side m p)) = capacity b ((side m p).testBit 0) :=
      beq_iff_eq.mp h
    have fun_eq : incidence m p = contains (side m p) := funext (fun _ => by simp only [incidence, yes, if_true])
    rw [fun_eq,exactCount,mark]
    exact Nat.le_refl _

  · simp only [incidence, Bool.not_eq_true] at *
    have z : total (sets b) (fun s => incidence m p s) = 0 := by
      simp [incidence,yes,total_zero]
    simp [z]

theorem one_color (b : Bool) (m : Nat → Nat) (r : Fin 8)
    (one : ∀ i < 8, (m i).testBit 0 = (i == r.val)) :
    total (sets b) (misses m) ≤ cap b := by
  unfold misses
  rw [transpose]
  have h := total_mono picks _ _ (fun p hp => one_pick b m r.val one p hp)
  have v := beq_iff_eq.mp (List.all_eq_true.mp (budgets b) r.val (List.mem_range.mpr r.isLt))
  rw [v] at h
  exact h

theorem count_zero {α : Type} (xs : List α) (f : α → Nat) :
    xs.length ≤ (xs.filter (fun x => f x == 0)).length + total xs f := by
  induction xs with
  | nil => simp [total]
  | cons x xs ih =>
    by_cases h : f x = 0
    · simp [h,total_cons,List.filter_cons]; omega
    · simp [h,total_cons,List.filter_cons]; omega

theorem many_seven_sets (b : Bool) (ms : List (Nat → Nat)) (len : ms.length = 15)
    (rows : ∀ m ∈ ms, ∃ r : Fin 8, ∀ i < 8, (m i).testBit 0 = (i == r.val)) :
    lower b ≤ ((sets b).filter (fun z => total ms (fun m => misses m z) == 0)).length := by
  have h := total_mono ms (fun m => total (sets b) (misses m)) (fun _ => cap b)
    (fun m hm => by obtain ⟨r,hr⟩ := rows m hm; exact one_color b m r hr)
  rw [constant_total ms (fun _ => cap b) (cap b) (fun _ _ => rfl),len] at h
  have t := count_zero (sets b) (fun z => total ms (fun m => misses m z))
  rw [transpose,sizes] at t
  change (total ms fun y => total (sets b) (fun x => misses y x)) ≤ 15 * cap b at h
  cases b <;> simp only [Bool.false_eq_true, if_true, if_false, cap, lower] at h t ⊢ <;> omega

#print axioms many_seven_sets
end SevenSet
