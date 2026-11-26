import SevenMore
import RawMenu
namespace WildMenu
open WildCuts WildLoss EdgeWalk WildDeletion Finset
set_option maxHeartbeats 4000000
set_option maxRecDepth 500000

def choices {H : Type} : List H → List (List H)
  | [] => [[]]
  | j::tail => let t := choices tail; t ++ t.map (j::·)

private theorem choices_sum {H : Type} (f : H → Nat) (w : Nat → Nat) (ls : List H) (start : Nat) :
    tree w (ls.map f) start =
      ((choices ls).map (fun s => w (start+(s.map f).sum))).sum := by
  induction ls generalizing start with
  | nil => simp [tree,choices]
  | cons h t ih =>
    simp only [List.map_cons,choices,List.map_append,List.sum_append,List.map_map,
      Function.comp_def,List.sum_cons,Nat.add_assoc,tree,ih]

def name (i : Fin 9) : Fin 10 := ⟨i.val,by omega⟩
def first (i : Fin 9) := vertex (2*i.val)
def second (i : Fin 9) := vertex (2*i.val+1)
def names := (9 : Fin 10)::(List.finRange 9).map name

def slotEdges := (List.finRange 9).map (fun i => (first i,second i))
def actual (q : Equiv.Perm V) := slotEdges.map (fun e => (q e.1,q e.2))
def bucket (q : Equiv.Perm V) (h : Fin 10) :=
  ∑ x ∈ univ.filter (fun v : V => (pairs 19).tag v = h), 2^(q x).val

private theorem side_sum (q : Equiv.Perm V) (j : Finset (Fin 10)) :
    sideCodes q j = ∑ h ∈ j, bucket q h := by
  unfold sideCodes closedSides mask key side bucket
  simp only [Finset.sum_map]
  exact (Finset.sum_fiberwise_eq_sum_filter univ j (pairs 19).tag (fun x => 2^(q x).val)).symm

private theorem enum_score (q : Equiv.Perm V) (w : Nat → Nat) :
    ∑ j, w (sideCodes q j) = tree w (names.map (bucket q)) 0 := by
  let choices' := choices names
  have facts : (choices'.map List.toFinset).Nodup ∧
      (choices'.map List.toFinset).toFinset = univ ∧ ∀ j ∈ choices', j.Nodup := by native_decide
  rw [choices_sum,← facts.2.1,List.sum_toFinset _ facts.1,List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro j hj
  simp only [Function.comp_apply,Nat.zero_add,side_sum,List.sum_toFinset _ (facts.2.2 _ hj)]

private theorem pair_buckets (q : Equiv.Perm V) :
    bucket q 9 = RawMenu.pointKey (q 18) ∧ ∀ i : Fin 9, bucket q (name i) =
      RawMenu.pointKey (q (first i))+RawMenu.pointKey (q (second i)) := by
  have singleton : univ.filter (fun x : V => (pairs 19).tag x = 9) = {18} := by decide
  have double : ∀ i : Fin 9, univ.filter (fun x : V => (pairs 19).tag x = name i) = {first i,second i} ∧
      first i ≠ second i := by decide
  constructor
  · simp [bucket,singleton,RawMenu.pointKey,Nat.one_shiftLeft]
  · intro i
    have ⟨eq,ne⟩ := double i
    simp [bucket,eq,RawMenu.pointKey,Nat.one_shiftLeft,ne]

private theorem all_endpoints (q : Equiv.Perm V) :
    ((List.finRange 19).erase (q 18)).Perm (ends (actual q)) := by
  have original : (List.finRange 19).Perm ((18 : V)::ends slotEdges) := by decide
  have allq : (List.finRange 19).Perm ((List.finRange 19).map q) := by
    apply List.perm_of_nodup_nodup_toFinset_eq
    · exact List.nodup_finRange _
    · exact (List.nodup_finRange 19).map q.injective
    · ext x
      simp only [List.mem_toFinset,List.mem_finRange,List.mem_map,true_and,true_iff]
      exact ⟨q.symm x,q.apply_symm_apply _⟩
  have move := allq.trans (original.map q)
  have erase := move.erase (q 18)
  simpa [actual,ends,List.map_flatMap,List.flatMap_map,Function.comp_def] using erase

theorem loss_score (q : Equiv.Perm V) (w : Nat → Nat) : ∑ j, w (sideCodes q j) =
    score w [0,RawMenu.pointKey (q 18)] ((actual q).map (fun e => RawMenu.pointKey e.1+RawMenu.pointKey e.2)) := by
  rw [enum_score]
  obtain ⟨singleton,double⟩ := pair_buckets q
  simp [names,actual,slotEdges,score,tree,singleton,double,List.map_map,Function.comp_def]

/-- Each search starts with the actual missing point and explores all possible
partners for the first remaining point. A partial loss is a lower bound for
every completion because adding another pair preserves all earlier subsets. -/
theorem eight_budget_from_search (checked : ∀ v : V, RawMenu.run v = true)
    (bridge : ∀ s : Finset V, RawMenu.lost (mask s) = cap s.card - value hist (mask s))
    (q : Equiv.Perm V) : charge q ≤ 4274742 := by
  have found := WildLoss.check_sound RawMenu.lost RawMenu.pointKey 40695 9 _ _ _ (all_endpoints q) (checked (q 18))
  rw [← loss_score] at found
  have capTotal : (∑ j : Finset (Fin 10), cap ((closedSides q j).card)) = 4315437 := by
    simp only [closedSides,Finset.card_map]
    decide +kernel
  have split : (∑ j, RawMenu.lost (sideCodes q j))+charge q = 4315437 := by
    rw [← capTotal]
    unfold charge
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [show sideCodes q j = mask (closedSides q j) from rfl,bridge]
    exact Nat.sub_add_cancel (cut_caps (closedSides q j))
  omega
end WildMenu
