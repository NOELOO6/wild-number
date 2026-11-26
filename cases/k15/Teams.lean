import Std

/- A cut-counting certificate for two teams of eight. Point 0 is deleted
   on K15, and {1,8,9} is the initial triple. The two teams are 0..7 and
   8..15. Every edge and group is encoded by its vertex bitmask. -/
namespace Teams
set_option maxHeartbeats 0
set_option maxRecDepth 200000
abbrev Mask := Nat
abbrev Matching := List Mask
abbrev Grouping := List Mask

def bit (i : Nat) : Nat := 1 <<< i
def pair (i j : Nat) := bit i ||| bit j

def unorderedPairs {α β} (xs : List α) (f : α → α → β) : List β :=
  match xs with
  | [] => []
  | a::as => as.map (f a) ++ unorderedPairs as f

def unorderedTriples {α β} (xs : List α) (f : α → α → α → β) : List β :=
  match xs with
  | [] => []
  | a::as => unorderedPairs as (f a) ++ unorderedTriples as f

/-- Pair the first unused vertex with each possible partner. -/
def matchings : Nat → List Nat → List Matching
  | 0, xs => if xs.isEmpty then [[]] else []
  | _+1, [] => []
  | k+1, a::as => as.flatMap fun b =>
    (matchings k (as.erase b)).map (fun m => pair a b :: m)

def bijections : List Nat → List Nat → List Matching
  | [], ys => if ys.isEmpty then [[]] else []
  | a::as, ys => ys.flatMap fun b =>
    (bijections as (ys.erase b)).map (fun m => pair a b :: m)

def intra := (matchings 4 (List.range 8)).flatMap fun m =>
  (matchings 4 (List.range' 8 8)).map (m ++ ·)
def inter := bijections (List.range 8) (List.range' 8 8)

def anchor : Nat := bit 1 ||| bit 8 ||| bit 9
def attach : Matching → List Nat → List Grouping
  | [], ys => [[ys.foldl (fun u v => u ||| bit v) 0]]
  | t::ts, ys => ys.flatMap fun b =>
    (attach ts (ys.erase b)).map (fun gs => (t ||| bit b) :: gs)

def catalogue : List Grouping := (matchings 3 (List.range' 2 6)).flatMap fun m =>
  (attach m (List.range' 10 6)).map (anchor :: ·)
def cuts (g : Grouping) := g.map (· ||| 1) ++ unorderedPairs g (· ||| ·)
def closedSides (m : Matching) :=
  unorderedPairs m (· ||| ·) ++ unorderedTriples m (fun x y z => x ||| y ||| z)

def genuine (g : Grouping) : Bool :=
  g.length == 5 && g.all (fun t => !t.testBit 0 && t < 65536 &&
      ((List.range 16).filter (fun i => t.testBit i)).length == 3) &&
    g.foldl (· ||| ·) 0 == 65534

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

def hit (g : Grouping) (s : Mask) := if s ∈ cuts g then 1 else 0
def failures (g : Grouping) (m : Matching) := total (closedSides m) (hit g)
def freqTable : Array Nat := Id.run do
  let mut t := Array.replicate 65536 0
  for g in catalogue do
    for s in cuts g do
      t := t.modify s (· + 1)
  return t
def freq (s : Nat) := freqTable[s]?.getD 0
def support := (catalogue.flatMap cuts).eraseDups
def cost (m : Matching) := total (closedSides m) freq

theorem side_catalogue : catalogue.all (fun g => (cuts g).all support.contains) = true := by
  native_decide
theorem frequency_check : support.all (fun s => total catalogue (fun g => hit g s) == freq s) = true := by
  native_decide
theorem frequency_bound (s : Nat) : total catalogue (fun g => hit g s) ≤ freq s := by
  by_cases hs : s ∈ support
  · exact Nat.le_of_eq (beq_iff_eq.mp (List.all_eq_true.mp frequency_check s hs))
  · have hzero : ∀ g ∈ catalogue, hit g s = 0 := by
      intro g hg
      have hnot : s ∉ cuts g := fun hh =>
        hs (List.contains_iff_mem.mp (List.all_eq_true.mp (List.all_eq_true.mp side_catalogue g hg) s hh))
      simp [hit, hnot]
    rw [constant_total _ _ 0 hzero]
    simp

theorem cost_bound (m : Matching) : total catalogue (fun g => failures g m) ≤ cost m := by
  unfold failures cost
  rw [transpose catalogue (closedSides m) hit]
  exact total_mono _ _ _ (fun s _ => frequency_bound s)

def qa := pair 0 1
def qb := pair 8 9
def rootCross (m : Matching) := m.contains (pair 0 8) || m.contains (pair 0 9)
def otherCross (m : Matching) := m.contains (pair 1 8) || m.contains (pair 1 9)
def tagInside (m : Matching) : Nat :=
  if m.contains qa then (if m.contains qb then 6 else 1) else (if m.contains qb then 1 else 0)
def tagCross (m : Matching) : Nat :=
  if rootCross m then (if otherCross m then 6 else 3) else (if otherCross m then 4 else 2)
def budget : Nat → Nat
  | 0 => 96 | 1 => 216 | 2 => 60 | 3 => 0 | 4 => 300 | _ => 0

theorem checked_intra : intra.all (fun m => tagInside m == 6 || cost m == budget (tagInside m)) = true := by
  native_decide
theorem checked_inter : inter.all (fun m => tagCross m == 6 || cost m == budget (tagCross m)) = true := by
  native_decide
theorem catalogue_size : catalogue.length = 1800 := by native_decide
theorem proper_groups : catalogue.all genuine = true := by native_decide
theorem distinct_arrangements : catalogue.Nodup := by native_decide

/-- This also applies to arbitrary mixed colors whenever their total cut
    cost is small. It counts successful partitions for the actual matchings. -/
theorem many_repairs (ms : List Matching) (cheap : total ms cost ≤ 1752) :
    48 ≤ (catalogue.filter (fun g => total ms (failures g) == 0)).length := by
  have allCosts : total catalogue (fun g => total ms (failures g)) ≤ 1752 := by
    rw [transpose catalogue ms failures]
    exact Nat.le_trans (total_mono ms _ _ (fun m _ => cost_bound m)) cheap
  have bound (xs : List Grouping) : xs.length ≤
      (xs.filter (fun g => total ms (failures g) == 0)).length + total xs (fun g => total ms (failures g)) := by
    induction xs with
    | nil => simp [total]
    | cons g gs ih =>
      by_cases h : total ms (failures g) = 0
      · simp [h, total_cons, List.filter_cons]; omega
      · simp [h, total_cons, List.filter_cons]; omega
  have b := bound catalogue
  rw [catalogue_size] at b
  omega

theorem perm_sum {as bs : List Nat} (p : as.Perm bs) : as.sum = bs.sum := by
  induction p with
  | nil => rfl
  | cons a h ih => simp [ih]
  | swap x y l => simp [Nat.add_left_comm]
  | trans _ _ ih jh => exact ih.trans jh

structure Entry where
  m : Matching
  tag : Nat

def hasTag (x : Entry) : Prop :=
  (x.m ∈ intra ∧ x.tag = tagInside x.m ∧ x.tag ≠ 6) ∨
  (x.m ∈ inter ∧ x.tag = tagCross x.m ∧ x.tag ≠ 6)

theorem entry_cost (x : Entry) (h : hasTag x) : cost x.m = budget x.tag := by
  rcases h with ⟨ha,hb,hc⟩ | ⟨ha,hb,hc⟩
  · have hh := List.all_eq_true.mp checked_intra x.m ha
    rw [← hb] at hh; simpa [hc] using hh
  · have hh := List.all_eq_true.mp checked_inter x.m ha
    rw [← hb] at hh; simpa [hc] using hh

theorem total_map {α β : Type} (xs : List α) (f : α → β) (g : β → Nat) :
    total (xs.map f) g = total xs (fun x => g (f x)) := by simp [total, List.map_map, Function.comp_def]

/-- After choosing a good initial quartet the seven within-team colors
    give tags 0,0,0,0,0,1,1; the eight cross-team colors give
    2,2,2,2,3,3,4,4, in any order. -/
theorem split_colorings (xs : List Entry) (h : ∀ x ∈ xs, hasTag x)
    (counts : (xs.map Entry.tag).Perm [0,0,0,0,0,1,1,2,2,2,2,3,3,4,4]) :
    48 ≤ (catalogue.filter (fun g => total (xs.map Entry.m) (failures g) == 0)).length := by
  apply many_repairs
  rw [total_map]
  have same := total_mono xs (fun x => cost x.m) (fun x => budget x.tag)
      (fun x hx => Nat.le_of_eq (entry_cost x (h x hx)))
  have counts' := perm_sum (counts.map budget)
  have b : total (xs.map Entry.tag) budget = 1752 := by
    exact counts'.trans (by decide)
  rw [total_map] at b
  omega

#print axioms split_colorings
end Teams
