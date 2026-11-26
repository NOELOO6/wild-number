import Teams
namespace FiveTeams
open Teams
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def perms : Nat → List Nat → List (List Nat)
  | 0, _ => [[]]
  | k+1, xs => xs.flatMap fun x => (perms k (xs.erase x)).map (x :: ·)
def team (i : Nat) := List.range' (1+3*i) 3
def whole (i : Nat) := 7 <<< (1+3*i)
def sent (i n : Nat) := bit (1+3*i+n/3^i%3)
def grouping (p : List Nat) (n : Nat) := (List.range 5).map fun i =>
  let a := p[i]!
  (whole a ^^^ sent a n) ||| sent (p[(i+4)%5]!) n
def cycles := (perms 4 [1,2,3,4]).map (0 :: ·)
def layouts := cycles.flatMap fun p => (List.range 243).map (grouping p)
def frequency := layouts.foldl (fun (a : Array Nat) g =>
  (cuts g).foldl (fun b s => b.modify s (·+1)) a) (Array.replicate 65536 0)
def price (m : Matching) := total (closedSides m) (fun s => frequency[s]!)
def pure := (List.range 5).flatMap fun i => (team i).flatMap fun h =>
  let rest := (List.range 5).erase i
  (rest.tail).flatMap fun j =>
    let a := rest[0]!
    let xs := (rest.erase a).erase j
    (bijections (team a) (team j)).flatMap fun m =>
      (bijections (team xs[0]!) (team xs[1]!)).map fun n =>
        pair 0 h :: ((team i).erase h).foldl (fun s v => s ||| bit v) 0 :: m ++ n

theorem buildings : cycles.length = 24 ∧ layouts.length = 5832 ∧
    layouts.all genuine = true ∧ layouts.Nodup := by native_decide
theorem pure_price : pure.length = 1620 ∧ pure.all (fun m => price m == 216) = true := by native_decide
theorem largest_price : (matchings 7 (List.range' 2 14)).all
    (fun m => price (pair 0 1 :: m) ≤ 1728) = true := by native_decide

def support := (List.range 65536).filter fun s => frequency[s]! != 0
theorem supported : layouts.all (fun g => (cuts g).all fun s => decide (s < 65536) && frequency[s]! != 0) = true := by native_decide
theorem table_correct : support.all (fun s => total layouts (fun g => hit g s) == frequency[s]!) = true := by native_decide
theorem count_side (s : Nat) : total layouts (fun g => hit g s) ≤ frequency[s]! := by
  by_cases h : s ∈ support
  · exact Nat.le_of_eq (beq_iff_eq.mp (List.all_eq_true.mp table_correct s h))
  · have zero : ∀ g ∈ layouts, hit g s = 0 := by
      intro g hg
      have none : s ∉ cuts g := by
        intro hs
        have pos := List.all_eq_true.mp (List.all_eq_true.mp supported g hg) s hs
        have both := Bool.and_eq_true_iff.mp pos
        exact h (List.mem_filter.mpr ⟨List.mem_range.mpr (of_decide_eq_true both.1),both.2⟩)
      simp [hit, none]
    rw [constant_total _ _ 0 zero]; simp
theorem each_price (m : Matching) : total layouts (fun g => failures g m) ≤ price m := by
  unfold failures price
  rw [transpose layouts (closedSides m) hit]
  exact total_mono _ _ _ (fun s _ => count_side s)

theorem budget (ms : List Matching) : layouts.length ≤
    (layouts.filter (fun g => total ms (failures g) == 0)).length + total ms price := by
  have index (xs : List Grouping) : xs.length ≤
      (xs.filter (fun g => total ms (failures g) == 0)).length + total xs (fun g => total ms (failures g)) := by
    induction xs with
    | nil => simp [total]
    | cons g gs ih =>
      by_cases h : total ms (failures g) = 0 <;> simp [h, total_cons, List.filter_cons] <;> omega
  have h := index layouts
  rw [transpose layouts ms failures] at h
  have m := total_mono ms _ _ (fun x _ => each_price x)
  omega

theorem five_teams (ms : List Matching) (count : ms.length = 15) (valid : ∀ m ∈ ms, m ∈ pure) :
    2592 ≤ (layouts.filter (fun g => total ms (failures g) == 0)).length := by
  have sum := constant_total ms price 216 (fun m hm =>
    beq_iff_eq.mp (List.all_eq_true.mp pure_price.2 m (valid m hm)))
  have h := budget ms
  rw [sum, count, buildings.2.1] at h
  omega
/-- Canonical labels for one arbitrary matching. Vertices in each team
    are interchangeable. Assign partners to a team's remaining vertices
    in nondecreasing order of partner team. -/
def teamOf (v : Nat) := (v-1)/3
def representatives : Nat → List Nat → Nat → Nat → List Matching
  | 0, [], _, _ => [[]]
  | k+1, a::xs, last, low =>
    (List.range 5).flatMap fun j =>
      if last == teamOf a && j < low then [] else
      match xs.find? (fun v => teamOf v == j) with
      | none => []
      | some b => (representatives k (xs.erase b) (teamOf a) j).map (pair a b :: ·)
  | _, _, _, _ => []
def profiles := (List.range 5).flatMap fun i =>
  let h := 1+3*i
  (representatives 7 ((List.range' 1 15).erase h) 5 0).map (pair 0 h :: ·)
def cells := (List.range 5).flatMap fun i => (List.range' i (5-i)).map (fun j => (i,j))
def entry (m : Matching) (i j : Nat) := total m fun e =>
  if i == j then
    if e &&& whole i == e then 2 else if e.testBit 0 && e &&& whole i != 0 then 1 else 0
  else if e &&& whole i != 0 && e &&& whole j != 0 then 1 else 0
def residue (m : Matching) (invert : Bool) := cells.foldl (fun a z =>
  let v := (entry m z.1 z.2)%3
  3*a+(if invert then (3-v)%3 else v)) 0
def entries := profiles.map (fun m => (residue m false,residue m true,price m))
theorem two_prices : profiles.length = 1345 ∧ entries.all (fun a => entries.all
    (fun b => a.1 != b.2.1 || a.2.2+b.2.2 ≤ 1872)) = true := by native_decide

theorem two_exceptions (ms : List Matching) (a b : Matching) (count : ms.length = 13)
    (valid : ∀ m ∈ ms, m ∈ pure) (pairPrice : price a + price b ≤ 1872) :
    1152 ≤ (layouts.filter (fun g => total (a::b::ms) (failures g) == 0)).length := by
  have sum := constant_total ms price 216 (fun m hm =>
    beq_iff_eq.mp (List.all_eq_true.mp pure_price.2 m (valid m hm)))
  have h := budget (a::b::ms)
  have v : total (a::b::ms) price = price a + (price b + 13*216) := by
    rw [total_cons, total_cons, sum, count]
  rw [v, buildings.2.1] at h
  omega

#print axioms two_prices
#print axioms five_teams
end FiveTeams
