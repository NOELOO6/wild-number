import Delete
namespace EdgeWalk
open WildDeletion
abbrev Edge (n : Nat) := Fin n × Fin n

def Adj {n} (es : List (Edge n)) (x y : Fin n) :=
  (x,y) ∈ es ∨ (y,x) ∈ es

def touch {n} (seen : Nat) (e : Edge n) :=
  if seen.testBit e.1.val || seen.testBit e.2.val then
    seen ||| 2^e.1.val ||| 2^e.2.val else seen

def run {n} (es : List (Edge n)) : Nat → Nat → Nat
  | 0, seen => seen
  | fuel+1, seen =>
    let more := es.foldl touch seen
    if more == seen then seen else run es fuel more

def passes {n} (root : Fin n) (es : List (Edge n)) :=
  run es n (2^root.val) == 2^n-1

private theorem symm {n} {es : List (Edge n)} {x y} (h : Adj es x y) :
    Adj es y x := h.symm

private theorem back {n} {es : List (Edge n)} {x y} (h : Walk (Adj es) x y) :
    Walk (Adj es) y x := by
  induction h with
  | stay => exact .stay _
  | step _ e ih => exact (Walk.step (.stay _) (symm e)).join ih

def Sound {n} (es : List (Edge n)) (root : Fin n) (s : Nat) :=
  ∀ v : Fin n, s.testBit v.val = true → Walk (Adj es) root v

private theorem touch_sound {n} {es : List (Edge n)} {root s} (hs : Sound es root s)
    (e : Edge n) (he : e ∈ es) : Sound es root (touch s e) := by
  unfold touch
  split
  · rename_i h
    have hxy : Adj es e.1 e.2 := Or.inl he
    have both : Walk (Adj es) root e.1 ∧ Walk (Adj es) root e.2 := by
      simp only [Bool.or_eq_true] at h
      rcases h with ha | hb
      · exact ⟨hs _ ha, .step (hs _ ha) hxy⟩
      · exact ⟨.step (hs _ hb) (symm hxy), hs _ hb⟩
    intro v hv
    simp only [Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow, decide_eq_true_eq] at hv
    rcases hv with (hv | hx) | hy
    · exact hs _ hv
    · exact Fin.ext hx ▸ both.1
    · exact Fin.ext hy ▸ both.2
  · exact hs

private theorem sweep_sound {n} {es : List (Edge n)} {root s} (hs : Sound es root s)
    (xs : List (Edge n)) (sub : ∀ e ∈ xs, e ∈ es) : Sound es root (xs.foldl touch s) := by
  induction xs generalizing s with
  | nil => exact hs
  | cons e xs ih =>
    exact ih (touch_sound hs e (sub e (by simp))) (fun t ht => sub t (by simp [ht]))

private theorem run_sound {n} {es : List (Edge n)} {root s} (hs : Sound es root s)
    (fuel : Nat) : Sound es root (run es fuel s) := by
  induction fuel generalizing s with
  | zero => exact hs
  | succ k ih =>
    simp only [run]
    split
    · exact hs
    · exact ih (sweep_sound hs es (fun _ h => h))

/-- A set bit in the computed search supplies a walk from the starting point. -/
theorem walk_of_seen {n} (root v : Fin n) (es : List (Edge n))
    (h : (run es n (2^root.val)).testBit v.val = true) : Walk (Adj es) root v := by
  apply run_sound (root:=root) _ n v h
  intro x hx
  have same : root = x := Fin.ext (by simpa [Nat.testBit_two_pow] using hx)
  subst x
  exact .stay _

theorem connected_of_passes {n} (root : Fin n) (es : List (Edge n))
    (h : passes root es = true) : Connected (Adj es) := by
  have start : Sound es root (2^root.val) := by
    intro v hv
    have he : root = v := Fin.ext (by simpa [Nat.testBit_two_pow] using hv)
    subst v
    exact .stay _
  have done := run_sound start n
  have eq : run es n (2^root.val) = 2^n-1 := beq_iff_eq.mp h
  rw [eq] at done
  have reaches (v : Fin n) := done v (by simp [Nat.testBit_two_pow_sub_one, v.isLt])
  exact fun a b => (back (reaches a)).join (reaches b)
end EdgeWalk
