import PairedCertificate
namespace Paired
open EdgeWalk WildDeletion
set_option interpreter.prefer_native true
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def insertEvery (a : Nat) : List Nat → List (List Nat)
  | [] => [[a]]
  | x::xs => (a::x::xs) :: (insertEvery a xs).map (x :: ·)
def orders : List Nat → List (List Nat)
  | [] => [[]]
  | a::xs => (orders xs).flatMap (insertEvery a)
def names := (orders (List.range 7)).map (fun l => (l++[7]).toArray)
def mate (p : P) (a : Nat) := projections[p.val]![a]!
def sends (r : Array Nat) (p q : P) := (List.range 8).all fun a => r[mate p a]! == mate q r[a]!
def naming (p : P) := names.filter (fun r => sends r p 0)
def genuine (a : Array Nat) := a.size == 8 && (List.range 8).all a.contains && a[7]! == 7

theorem names_valid : names.all genuine = true := by native_decide
theorem naming_works : ∀ p : P, (List.finRange 105).all (fun q =>
    mate q 7 != mate p 7 || (naming p).any fun r =>
      (List.finRange 3).any fun k => sends r q (special k)) = true := by native_decide

theorem three_normal_forms (p q : P) (h : mate q 7 = mate p 7) :
    ∃ r : Array Nat, genuine r = true ∧ sends r p 0 = true ∧ ∃ k : K, sends r q (special k) = true := by
  have allP : ∀ t : P, t ∈ List.finRange 105 := by native_decide
  have ok := List.all_eq_true.mp (naming_works p) q (allP q)
  simp only [h, bne_self_eq_false, Bool.false_or] at ok
  obtain ⟨r,hr,hk⟩ := List.any_eq_true.mp ok
  obtain ⟨hm,h0⟩ := List.mem_filter.mp hr
  obtain ⟨k,_,hs⟩ := List.any_eq_true.mp hk
  exact ⟨r,List.all_eq_true.mp names_valid _ hm,h0,k,hs⟩

/-- Every matching of the eight teams occurs among the 105 projections.
The next pair always starts with the least remaining team. -/
def teamMatchings : Nat → List Nat → List (List (Nat × Nat))
  | _, [] => [[]]
  | 0, _::_ => []
  | d+1, a::xs => xs.flatMap fun b => (teamMatchings d (xs.erase b)).map ((a,b) :: ·)
inductive TeamMatching : List Nat → List (Nat × Nat) → Prop where
  | nil : TeamMatching [] []
  | pair {a b xs t} (hb : b ∈ xs) (next : TeamMatching (xs.erase b) t) :
      TeamMatching (a::xs) ((a,b)::t)
theorem generate_all_teams {xs m} (h : TeamMatching xs m) (n : Nat) (hn : m.length ≤ n) :
    m ∈ teamMatchings n xs := by
  induction h generalizing n with
  | nil => cases n <;> simp [teamMatchings]
  | @pair a b xs t hb _ ih =>
    cases n with
    | zero => simp at hn
    | succ n => exact List.mem_flatMap.mpr ⟨b,hb, List.mem_map.mpr ⟨t,ih n (by simpa using hn),rfl⟩⟩
theorem catalogue_complete : (List.finRange 105).map pairs = teamMatchings 4 (List.range 8) := by native_decide
theorem every_team_matching_has_name (m) (h : TeamMatching (List.range 8) m) (n : m.length = 4) :
    ∃ p : P, pairs p = m := by
  have hm := generate_all_teams h 4 (Nat.le_of_eq n)
  rw [← catalogue_complete] at hm
  obtain ⟨p,_,eq⟩ := List.mem_map.mp hm
  exact ⟨p,eq⟩

/-- Putting the deleted point back as a leaf in each color keeps the very
same ten wild edges, all on the fifteen old vertices. -/
theorem ten_with_point_restored (k : K) (sa sb : Fin 16) (rest : List C)
    (cover : ((rest.map (fun c => pairIds c.1)).flatten).Perm (residual k))
    (neighbor : Edges → V) :
    ∃ w : Edges, w.length = 10 ∧ ∀ m ∈ (anchor :: color (0,sa) :: color (special k,sb) :: rest.map color),
      Connected (withLeaf (Adj (w ++ m)) (neighbor m)) := by
  obtain ⟨w,hw,ha,hb,hc,hr⟩ := ten_for_paired_colors k sa sb rest cover
  refine ⟨w,hw,fun m hm => (leaf_iff _ _).mpr ?_⟩
  simp only [List.mem_cons, List.mem_map] at hm
  rcases hm with rfl | rfl | rfl | ⟨c,ht,rfl⟩
  · exact ha
  · exact hb
  · exact hc
  · exact hr c ht
#print axioms three_normal_forms
#print axioms ten_with_point_restored
end Paired
