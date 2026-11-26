import Paired
namespace Paired
open EdgeWalk WildDeletion
set_option interpreter.prefer_native true
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem individual_costs : ∀ k : K, ∀ p : P, ∀ s : Fin 16,
    cost (sched k) (color (p,s)) ≤ charge k p := by native_decide

theorem anchor_and_two : ∀ k : K, (sched k).all (fun (_,w) => w.length == 10 &&
    passes 0 (w ++ anchor) && (List.finRange 16).all fun s =>
      passes 0 (w ++ color (0,s)) && passes 0 (w ++ color (special k,s))) = true := by native_decide

theorem budget : ∀ k : K, ((residual k).map (price k)).sum < weight (sched k) := by native_decide

def sumBy {α : Type} (xs : List α) (f : α → Nat) := (xs.map f).sum
private theorem addBy {α} (xs : List α) (f g : α → Nat) :
    sumBy xs (fun x => f x + g x) = sumBy xs f + sumBy xs g := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [sumBy, List.map_cons, List.sum_cons] at ih ⊢; omega

private theorem commute {α β} (xs : List α) (ys : List β) (f : α → β → Nat) :
    sumBy xs (fun x => sumBy ys (f x)) = sumBy ys (fun y => sumBy xs (fun x => f x y)) := by
  induction xs with
  | nil =>
    change 0 = (ys.map (fun _ => 0)).sum
    induction ys with
    | nil => rfl
    | cons y ys ih => simpa using ih
  | cons x xs ih =>
    change sumBy ys (f x) + sumBy xs _ = sumBy ys (fun y => f x y + sumBy xs _)
    rw [ih, addBy]

private theorem sum_mono {α} {f g : α → Nat} (xs : List α) (h : ∀ x ∈ xs, f x ≤ g x) :
    sumBy xs f ≤ sumBy xs g := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
    exact Nat.add_le_add (h _ (by simp)) (ih (fun y hy => h y (by simp [hy])))

private theorem term_le {α} (f : α → Nat) {x : α} {xs : List α} (h : x ∈ xs) :
    f x ≤ sumBy xs f := by
  induction xs with
  | nil => contradiction
  | cons y ys ih =>
    change f x ≤ f y + sumBy ys f
    rcases List.mem_cons.mp h with rfl | ht
    · omega
    · have := ih ht; omega

private theorem sum_perm {xs ys : List Nat} (h : xs.Perm ys) : xs.sum = ys.sum := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap => simp only [List.sum_cons]; omega
  | trans _ _ a b => exact a.trans b

private theorem sum_append (xs ys : List Nat) : (xs++ys).sum = xs.sum+ys.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.add_assoc]

private theorem pay (k : K) (cs : List C) :
    sumBy cs (fun c => charge k c.1) = (((cs.map (fun c => pairIds c.1)).flatten).map (price k)).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    change charge k c.1 + sumBy cs _ = _
    simp only [List.map_cons, List.flatten_cons, List.map_append, sum_append]
    exact congrArg (charge k c.1 + ·) ih

/-- Any compatible selection of lifted colors spends fewer failures than there
are layout tickets. One ticket connects the anchor and every selected color. -/
theorem ten_for_paired_colors (k : K) (sa sb : Fin 16) (rest : List C)
    (cover : ((rest.map (fun c => pairIds c.1)).flatten).Perm (residual k)) :
    ∃ w : Edges, w.length = 10 ∧ Connected (Adj (w ++ anchor)) ∧
      Connected (Adj (w ++ color (0,sa))) ∧ Connected (Adj (w ++ color (special k,sb))) ∧
      ∀ c ∈ rest, Connected (Adj (w ++ color c)) := by
  have small : sumBy rest (fun c => cost (sched k) (color c)) < weight (sched k) := by
    apply Nat.lt_of_le_of_lt (sum_mono rest (fun c _ => individual_costs k c.1 c.2))
    rw [pay, sum_perm (cover.map (price k))]
    exact budget k
  have existsRow : ∃ r ∈ sched k, ∀ c ∈ rest, passes 0 (r.2 ++ color c) = true := by
    apply Classical.byContradiction
    intro hn
    have lo : weight (sched k) ≤ sumBy (sched k)
        (fun (r : Nat × Edges) => sumBy rest (fun c => r.1 * failure r.2 (color c))) := by
      apply sum_mono
      intro r hr
      by_cases hb : ∃ c ∈ rest, passes 0 (r.2 ++ color c) = false
      · obtain ⟨c,hc,fail⟩ := hb
        have h := term_le (fun t => r.1 * failure r.2 (color t)) hc
        simpa [failure, fail] using h
      · exact False.elim (hn ⟨r,hr,fun c hc => by cases he : passes 0 (r.2 ++ color c) <;> simp_all⟩)
    rw [commute] at lo
    exact Nat.not_le_of_gt small lo
  obtain ⟨⟨t,w⟩,hw,ok⟩ := existsRow
  have base := List.all_eq_true.mp (anchor_and_two k) (t,w) hw
  simp only [Bool.and_eq_true, beq_iff_eq] at base
  have allSign : ∀ s : Fin 16, s ∈ List.finRange 16 := by decide
  have a := Bool.and_eq_true_iff.mp (List.all_eq_true.mp base.2 sa (allSign sa))
  have b := Bool.and_eq_true_iff.mp (List.all_eq_true.mp base.2 sb (allSign sb))
  exact ⟨w, base.1.1, connected_of_passes 0 _ base.1.2, connected_of_passes 0 _ a.1,
    connected_of_passes 0 _ b.2, fun c hc => connected_of_passes 0 _ (ok c hc)⟩
#print axioms ten_for_paired_colors
end Paired
