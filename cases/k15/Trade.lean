import Teams

/- Six within-team and seven cross-team matchings are arbitrary. The remaining
   two colors share the edges of a within-team and a cross-team matching.
   At most one proposed blue point can spoil the anchor for a pure color. -/
namespace Trade
open Teams
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def blue := List.range' 8 8
def candidates := List.range' 9 7
def bval (b : Bool) : Nat := if b then 1 else 0
def edgeUse (m : Matching) (x y : Nat) := bval (m.contains (pair x y))
def usage (ms : List Matching) (x y : Nat) := total ms (edgeUse · x y)
def bad (m : Matching) (z : Nat) := edgeUse m 1 8 * edgeUse m 0 z
def miss (ms : List Matching) (z : Nat) := total ms (bad · z)

/-- Exchange the proposed blue point with point 9, the fixed catalogue label. -/
def change (z e : Nat) := if e.testBit 9 != e.testBit z then
  e ^^^ (bit 9 ||| bit z) else e
def rename (z : Nat) (m : Matching) := m.map (change z)
def expense (z : Nat) (m : Matching) := cost (rename z m)

def redEdges := (List.range 4).map (fun i => pair (2*i) (2*i+1))
def diagonal := (List.range 8).map (fun i => pair i (8+i))
def blues := matchings 4 blue
def switched (code : Nat) := (List.range 16).foldl (fun a i =>
  if code.testBit ((i%8)/2) then a ||| bit i else a) 0
def closed (s : Nat) (m : Matching) := m.all (fun e => (e &&& s) == 0 || (e &&& s) == e)
def mixed (q : Matching) (code : Nat) : Matching × Matching :=
  let s := switched code
  let w := redEdges ++ q
  let take := fun e => (e &&& s) != 0
  (w.filter take ++ diagonal.filter (fun e => !take e),
   diagonal.filter take ++ w.filter (fun e => !take e))

/-- How often the thirteen pure colors can spoil a grouping, assuming the
    one potentially bad cross-team anchor has been avoided. -/
def pureBudget (q : Matching) (z : Nat) :=
  6*96 + 120*(1-edgeUse q 8 z) + (7*60-60) + 240*(1+bval (z != 9))
def budget (q : Matching) (code z : Nat) :=
  let pair' := mixed q code
  pureBudget q z + expense z pair'.1 + expense z pair'.2

theorem cheap_choices : blues.all (fun q => (List.range' 1 14).all (fun code =>
    !closed (switched code) q ||
    5 ≤ (candidates.filter (fun z => budget q code z ≤ 1776)).length)) = true := by native_decide
theorem profile_count : total blues (fun q => ((List.range' 1 14).filter
    (fun code => closed (switched code) q)).length) = 174 := by native_decide

theorem within_tables : intra.all (fun m => m.contains (pair 0 1) ||
    candidates.all (fun z => expense z m == 96+120*edgeUse m 8 z)) = true := by native_decide
theorem cross_tables : inter.all (fun m => m.contains (pair 0 8) || m.contains (pair 1 9) ||
    candidates.all (fun z => bad m z != 0 ||
    expense z m + 60*edgeUse m 0 z == 60 + 240*edgeUse m 1 8 + 240*edgeUse m 1 z)) = true := by native_decide
theorem bad_tables : inter.all (fun m =>
    total candidates (bad m) ≤ edgeUse m 1 8) = true := by native_decide

theorem all_within (ms : List Matching) (z : Nat) (hz : z ∈ candidates)
    (h : ∀ m ∈ ms, m ∈ intra ∧ m.contains (pair 0 1) = false) :
    total ms (expense z) = 96*ms.length+120*usage ms 8 z := by
  induction ms with
  | nil => simp [total, usage]
  | cons m ms ih =>
    obtain ⟨hm,hn⟩ := h m (by simp)
    have t := List.all_eq_true.mp within_tables m hm
    rw [hn, Bool.false_or] at t
    have here := beq_iff_eq.mp (List.all_eq_true.mp t z hz)
    have rest := ih (by intro a ha; exact h a (by simp [ha]))
    simp only [usage, total_cons, List.length_cons] at rest ⊢
    omega

theorem all_cross (ms : List Matching) (z : Nat) (hz : z ∈ candidates)
    (h : ∀ m ∈ ms, m ∈ inter ∧ m.contains (pair 0 8) = false ∧ m.contains (pair 1 9) = false)
    (safe : miss ms z = 0) :
    total ms (expense z) + 60*usage ms 0 z =
    60*ms.length + 240*usage ms 1 8 + 240*usage ms 1 z := by
  induction ms with
  | nil => simp [total, usage]
  | cons m ms ih =>
    obtain ⟨hm,hn,hn'⟩ := h m (by simp)
    change bad m z + miss ms z = 0 at safe
    have zero : bad m z = 0 := by omega
    have t := List.all_eq_true.mp cross_tables m hm
    rw [hn, hn', Bool.false_or, Bool.false_or] at t
    have here := List.all_eq_true.mp t z hz
    simp [zero] at here
    have rest := ih (by intro a ha; exact h a (by simp [ha])) (by omega)
    simp only [usage, total_cons, List.length_cons] at rest ⊢
    omega

theorem at_most_one (ms : List Matching) (pure : ∀ m ∈ ms, m ∈ inter)
    (unique : usage ms 1 8 = 1) : total candidates (miss ms) ≤ 1 := by
  unfold miss
  rw [transpose]
  rw [← unique]
  exact total_mono ms _ _ (fun m hm => of_decide_eq_true (List.all_eq_true.mp bad_tables m (pure m hm)))

theorem count_good {α : Type} (xs : List α) (f : α → Nat) :
    xs.length ≤ (xs.filter (fun x => f x == 0)).length + total xs f := by
  induction xs with
  | nil => simp [total]
  | cons x xs ih =>
    by_cases h : f x = 0
    · simp [h,total_cons,List.filter_cons]; omega
    · simp [h,total_cons,List.filter_cons]; omega

theorem filtered_total {α : Type} (xs : List α) (p : α → Bool) (f : α → Nat) :
    total (xs.filter p) f ≤ total xs f := by
  induction xs with
  | nil => simp [total]
  | cons x xs ih =>
    cases h : p x <;> simp [h,List.filter_cons,total_cons] <;> omega

theorem enough (ms : List Matching) (cheap : total ms cost ≤ 1776) :
    24 ≤ (catalogue.filter (fun g => total ms (failures g) == 0)).length := by
  have bound : total catalogue (fun g => total ms (failures g)) ≤ 1776 := by
    rw [transpose catalogue ms failures]
    exact Nat.le_trans (total_mono ms _ _ (fun m _ => cost_bound m)) cheap
  have t := count_good catalogue (fun g => total ms (failures g))
  rw [catalogue_size] at t
  omega

/-- These are the individual edge counts forced by covering the two complete
    teams except for the reserved within matching and the reserved diagonal. -/
structure PurePart (q : Matching) (inside across : List Matching) : Prop where
  ni : inside.length = 6
  nc : across.length = 7
  inner : ∀ m ∈ inside, m ∈ intra ∧ m.contains (pair 0 1) = false
  outer : ∀ m ∈ across, m ∈ inter ∧ m.contains (pair 0 8) = false ∧ m.contains (pair 1 9) = false
  blueEdge : ∀ z ∈ candidates, usage inside 8 z = 1-edgeUse q 8 z
  rootEdge : ∀ z ∈ candidates, usage across 0 z = 1
  otherEdge : ∀ z ∈ candidates, usage across 1 z = bval (z != 9)
  one : usage across 1 8 = 1

def allColors (inside across : List Matching) (q : Matching) (code z : Nat) :=
  ((inside ++ across) ++ [(mixed q code).1, (mixed q code).2]).map (rename z)

theorem four_choices (inside across : List Matching) (q : Matching) (code : Nat)
    (hq : q ∈ blues) (hc : code ∈ List.range' 1 14) (valid : closed (switched code) q = true)
    (f : PurePart q inside across) :
    4 ≤ ((candidates.filter (fun z => budget q code z ≤ 1776)).filter
      (fun z => miss across z == 0)).length := by
  have t := List.all_eq_true.mp (List.all_eq_true.mp cheap_choices q hq) code hc
  simp [valid] at t
  have h := at_most_one across (fun m hm => (f.outer m hm).1) f.one
  have hh := filtered_total candidates (fun z => decide (budget q code z ≤ 1776)) (miss across)
  have r := count_good (candidates.filter (fun z => budget q code z ≤ 1776)) (miss across)
  omega

theorem works (inside across : List Matching) (q : Matching) (code z : Nat)
    (f : PurePart q inside across) (hz : z ∈ candidates)
    (cheap : budget q code z ≤ 1776) (safe : miss across z = 0) :
    24 ≤ (catalogue.filter (fun g => total (allColors inside across q code z) (failures g) == 0)).length := by
  apply enough
  have i := all_within inside z hz f.inner
  have c := all_cross across z hz f.outer safe
  rw [f.ni, f.blueEdge z hz] at i
  rw [f.nc, f.rootEdge z hz, f.one, f.otherEdge z hz] at c
  unfold allColors
  rw [total_map]
  change total ((inside ++ across) ++ [(mixed q code).1,(mixed q code).2]) (expense z) ≤ 1776
  have append (a b : List Matching) : total (a++b) (expense z) =
      total a (expense z) + total b (expense z) := by
    induction a with
    | nil => simp [total]
    | cons x xs ih => simp only [List.cons_append,total_cons,ih,Nat.add_assoc]
  rw [append,append,total_cons,total_cons]
  simp only [total_nil, Nat.add_zero]
  simp only [budget, pureBudget] at cheap
  omega

theorem every_exchange (inside across : List Matching) (q : Matching) (code : Nat)
    (hq : q ∈ blues) (hc : code ∈ List.range' 1 14) (valid : closed (switched code) q = true)
    (f : PurePart q inside across) :
    ∃ z ∈ candidates, ∃ g ∈ catalogue, total (allColors inside across q code z) (failures g) = 0 := by
  let good := (candidates.filter (fun z => budget q code z ≤ 1776)).filter
       (fun z => miss across z == 0)
  have h : 4 ≤ good.length := four_choices inside across q code hq hc valid f
  obtain ⟨z,hz⟩ := List.exists_mem_of_length_pos (show 0 < good.length by omega)
  obtain ⟨hz',safe⟩ := List.mem_filter.mp hz
  obtain ⟨hcand,cheap⟩ := List.mem_filter.mp hz'
  have enoughSets := works inside across q code z f hcand (of_decide_eq_true cheap) (beq_iff_eq.mp safe)
  obtain ⟨g,hg⟩ := List.exists_mem_of_length_pos (Nat.lt_of_lt_of_le (by decide : 0 < 24) enoughSets)
  obtain ⟨hcat,hzero⟩ := List.mem_filter.mp hg
  exact ⟨z,hcand,g,hcat,beq_iff_eq.mp hzero⟩

#print axioms every_exchange
#print axioms four_choices
#print axioms works
end Trade
