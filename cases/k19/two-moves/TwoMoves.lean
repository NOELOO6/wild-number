import Example19
namespace K19Exchange
open Finset EdgeWalk WildDeletion
abbrev G := Fin 6

/-- One block of four vertices followed by five blocks of three. -/
def tag (x : V) : G := ⟨(x.val-1)/3,by omega⟩
def verts (i : G) := univ.filter (fun x => tag x = i)
def cuts (i : G) := (verts i).powerset.filter (fun s => s.Nonempty ∧ s ≠ verts i)
def lines (i : G) := (univ : Finset E).filter (fun e => e.1 < e.2 ∧ tag e.1 = i ∧ tag e.2 = i)
def safe (s : Finset V) (e : E) : Bool := decide (e.1 ∈ s ↔ e.2 ∈ s)
def internal := (List.finRange 19).flatMap fun x =>
  ((List.finRange 19).filter (fun y => x < y && tag x == tag y)).map (fun y => (x,y))
def retained (s : Finset V) := internal.filter (safe s)
def need (i : G) := if i = 0 then 3 else 2

theorem small_block : ∀ i : G, ∀ z : ↥((lines i).powerset), z.val.card < need i →
    ∃ s : ↥(cuts i), ∀ e ∈ z.val, safe s.val e = true := by native_decide

theorem every_split : ∀ i : G, ∀ s : ↥(cuts i), ∀ e : E, rejects (e::retained s.val) = true := by
  native_decide

theorem mem_internal (e : E) : e ∈ internal ↔ e.1 < e.2 ∧ tag e.1 = tag e.2 := by
  have all : ∀ p : E, p ∈ internal ↔ p.1 < p.2 ∧ tag p.1 = tag p.2 := by native_decide
  exact all e

/-- Twelve lines inside the original blocks and one line anywhere cannot
connect all nineteen colors, even if the twelve internal lines are reselected. -/
theorem twelve_and_one (old : List E) (length : old.length ≤ 12)
    (inside : ∀ e ∈ old, e ∈ internal) (extra : E) :
    ¬ ∀ c, Connected (Adj ((extra::old) ++ color c)) := by
  let t := old.toFinset
  let chunk (i : G) := t.filter (fun e => tag e.1 = i)
  have mass : ∑ i, (chunk i).card = t.card :=
    (Finset.card_eq_sum_card_fiberwise (f := fun e : E => tag e.1) (fun _ _ => Finset.mem_univ _)).symm
  have sumNeed : ∑ i, need i = 13 := by decide
  have upper : t.card ≤ 12 := le_trans (List.toFinset_card_le old) length
  have low : ∑ i, (chunk i).card < ∑ i, need i := by omega
  obtain ⟨i,_,hi⟩ := Finset.exists_lt_of_sum_lt low
  have sub : chunk i ⊆ lines i := by
    intro e he
    obtain ⟨ht,eq⟩ := Finset.mem_filter.mp he
    have h := (mem_internal e).mp (inside e (List.mem_toFinset.mp ht))
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.1,eq,h.2.symm.trans eq⟩
  obtain ⟨s,hs⟩ := small_block i ⟨chunk i, Finset.mem_powerset.mpr sub⟩ hi
  have ss := Finset.mem_powerset.mp (Finset.mem_filter.mp s.property).1
  have incl (e : E) (he : e ∈ old) : e ∈ retained s.val := by
    have ins := inside e he
    refine List.mem_filter.mpr ⟨ins,?_⟩
    by_cases h : tag e.1 = i
    · exact hs e (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr he,h⟩)
    · have right := (mem_internal e).mp ins
      have leftOut (hx : e.1 ∈ s.val) := h (Finset.mem_filter.mp (ss hx)).2
      have rightOut (hx : e.2 ∈ s.val) := h (right.2.trans (Finset.mem_filter.mp (ss hx)).2)
      exact decide_eq_true (⟨fun hx => (leftOut hx).elim, fun hx => (rightOut hx).elim⟩)
  intro paths
  apply rejected _ (every_split i s extra)
  intro c x y
  have mono {p : E} (hp : p ∈ (extra::old) ++ color c) : p ∈ (extra::retained s.val) ++ color c := by
    simp only [List.mem_append,List.mem_cons] at hp ⊢
    exact hp.imp (fun q => q.imp_right (incl p)) id
  have w := paths c x y
  induction w with
  | stay => exact .stay _
  | step _ ha ih => exact .step ih (ha.imp mono mono)

theorem every_single_move (line : E) (h : line ∈ start) (extra : E) :
    ¬ ∀ c, Connected (Adj ((extra::start.erase line) ++ color c)) := by
  apply twelve_and_one
  · rw [List.length_erase_of_mem h]
    decide
  · intro e he
    have all : ∀ p ∈ start, p ∈ internal := by native_decide
    exact all e (List.mem_of_mem_erase he)

#print axioms twelve_and_one
#print axioms every_single_move
end K19Exchange
