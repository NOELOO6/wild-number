import Std
namespace K17Incidence

/-- Unordered selections of r positions, in the order of the input list. -/
def picks {α : Type} : List α → Nat → List (List α)
  | [], 0 => [[]]
  | [], _+1 => []
  | _::_, 0 => [[]]
  | x::xs, r+1 => picks xs (r+1) ++ (picks xs r).map (x :: ·)

def choose : Nat → Nat → Nat
  | 0, 0 => 1
  | 0, _+1 => 0
  | _+1, 0 => 1
  | n+1, r+1 => choose n (r+1) + choose n r

theorem count_picks {α : Type} (cs : List α) (p : α → Bool) (r : Nat) :
    ((picks cs r).filter (fun s => s.all p)).length = choose (cs.filter p).length r := by
  induction cs generalizing r with
  | nil => cases r <;> rfl
  | cons c cs ih =>
    cases r with
    | zero =>
      simp only [picks, List.all_nil, List.filter_cons_of_pos, List.filter_nil, List.length_cons,
        List.length_nil]
      cases (List.filter p (c::cs)).length <;> rfl
    | succ r =>
      cases hc : p c <;>
        simp [picks, List.filter_map, Function.comp_def, hc, ih, choose, List.filter_cons]

def sumOn {α : Type} (xs : List α) (f : α → Nat) := (xs.map f).sum

private theorem addOn {α : Type} (xs : List α) (f g : α → Nat) :
    sumOn xs (fun x => f x+g x) = sumOn xs f + sumOn xs g := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [sumOn, List.map_cons, List.sum_cons] at ih ⊢; omega

private theorem transpose {α β : Type} (xs : List α) (ys : List β) (f : α → β → Nat) :
    sumOn xs (fun x => sumOn ys (f x)) = sumOn ys (fun y => sumOn xs (fun x => f x y)) := by
  induction xs with
  | nil =>
    change 0 = (ys.map (fun _ => 0)).sum
    induction ys with
    | nil => rfl
    | cons y ys ih => simpa only [List.map_cons, List.sum_cons, Nat.zero_add] using ih
  | cons x xs ih =>
    change sumOn ys (f x) + sumOn xs _ = sumOn ys (fun y => f x y + sumOn xs _)
    rw [ih, addOn]

private theorem indicator {α : Type} (xs : List α) (p : α → Bool) :
    (xs.filter p).length = sumOn xs (fun x => if p x then 1 else 0) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : p x <;> simp [List.filter_cons, sumOn, h, sumOn] at ih ⊢ <;> omega

/-- For any family of layouts and any failure relation, counting simultaneous
    failures by layout or by unordered color subset gives exactly the same sum. -/
theorem count_by_colors {Layout Color : Type} (ls : List Layout) (cs : List Color)
    (bad : Layout → Color → Bool) (r : Nat) :
    sumOn ls (fun l => choose (cs.filter (bad l)).length r) =
    sumOn (picks cs r) (fun colors => (ls.filter fun l => colors.all (bad l)).length) := by
  let hit := fun (l : Layout) (s : List Color) => if s.all (bad l) then 1 else 0
  calc
    _ = sumOn ls (fun l => sumOn (picks cs r) (hit l)) := by
      apply congrArg (sumOn ls)
      funext l
      rw [← count_picks, indicator]
    _ = sumOn (picks cs r) (fun s => sumOn ls (fun l => hit l s)) := transpose _ _ _
    _ = _ := by
      apply congrArg (sumOn (picks cs r))
      funext cs
      exact (indicator ls (fun l => cs.all (bad l))).symm

theorem first_three : ∀ k : Fin 18, choose k 1 = k.val ∧
    choose k 2 = k.val*(k.val-1)/2 ∧ choose k 3 = k.val*(k.val-1)*(k.val-2)/6 := by decide

private theorem perm_sum {xs ys : List Int} (h : xs.Perm ys) : xs.sum = ys.sum := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap => simp only [List.sum_cons]; omega
  | trans _ _ a b => exact a.trans b

private theorem append_sum (xs ys : List Int) : (xs++ys).sum = xs.sum+ys.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.cons_append, List.sum_cons, ih]; omega

/-- In a factorization the remaining matchings list every unused edge once.
    Summing a signed edge price color by color charges each unused edge once. -/
theorem charge_edges {E : Type} (colors : List (List E)) (unused : List E)
    (covers : colors.flatten.Perm unused) (price : E → Int) :
    (colors.map (fun c => (c.map price).sum)).sum = (unused.map price).sum := by
  have h : (colors.flatten.map price).sum = (unused.map price).sum := perm_sum (covers.map price)
  rw [← h]
  clear covers h
  induction colors with
  | nil => rfl
  | cons c cs ih => simp only [List.map_cons, List.sum_cons, List.flatten_cons, List.map_append, append_sum, ih]

#print axioms count_by_colors
#print axioms charge_edges
end K17Incidence
