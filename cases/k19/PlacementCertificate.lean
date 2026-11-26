import Placement
namespace K19Placement
set_option interpreter.prefer_native true
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem checked : table.toList.all (fun (s,v) => rowOK s v) = true := by native_decide
theorem initial : known start = true ∧ val start = 12760728035328000 ∧ table.size = 11305 := by native_decide

private theorem row {s : Shape} (h : known s = true) : rowOK s (val s) = true := by
  have hv : table[s]? = some (val s) := by
    unfold known at h
    rw [Std.HashMap.contains_eq_isSome_getElem?] at h
    unfold val
    cases eq : table[s]? <;> simp_all
  exact List.all_eq_true.mp checked (s,val s) (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hv)

theorem terminal {s : Shape} (h : known s = true) (z : freeSlots s = 0) :
    val s = s.length-1 := by simpa [rowOK,z] using row h

theorem conditional {s : Shape} (h : known s = true) (z : freeSlots s ≠ 0)
    {a : Option Nat} (ha : a ∈ actions s) :
    (tickets s a).all known = true ∧ ((tickets s a).map val).sum = val s := by
  have hr := row h
  simp [rowOK,z] at hr
  exact ⟨List.all_eq_true.mpr (hr a ha).1, (hr a ha).2⟩

set_option maxHeartbeats 400000

def sumBy {α : Type} (xs : List α) (f : α → Nat) := (xs.map f).sum
private theorem addBy {α} (xs : List α) (f g : α → Nat) :
    sumBy xs (fun x => f x + g x) = sumBy xs f + sumBy xs g := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [sumBy, List.map_cons, List.sum_cons] at ih ⊢; omega
private theorem transpose {α β} (xs : List α) (ys : List β) (f : α → β → Nat) :
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
private theorem permSum {xs ys : List Nat} (h : xs.Perm ys) : xs.sum = ys.sum := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap => simp only [List.sum_cons]; omega
  | trans _ _ a b => exact a.trans b
private theorem total_floor {α} {f : α → Nat} {k : Nat} (xs : List α) (h : ∀ x ∈ xs, k ≤ f x) :
    xs.length*k ≤ sumBy xs f := by
  induction xs with
  | nil => simp [sumBy]
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.length_cons, Nat.succ_mul, sumBy, List.map_cons, List.sum_cons] at ht ⊢
    omega

def fac : Nat → Nat
  | 0 => 1
  | n+1 => (n+1)*fac n

/-- The children are the choices of the next slot. The same child is chosen
for all colors. Each color may open an edge or close a different waiting edge. -/
structure Game (X : Type) where
  children : X → List X
  left : X → Nat
  shape : X → Fin 19 → Shape
  slots : ∀ x c, freeSlots (shape x c) = left x
  count : ∀ x, left x ≠ 0 → (children x).length = left x
  fewer : ∀ x y, y ∈ children x → left y + 1 = left x
  outcomes : ∀ x c, left x ≠ 0 → ∃ a ∈ actions (shape x c),
    ((children x).map (fun y => shape y c)).Perm (tickets (shape x c) a)

inductive Desc {X : Type} (g : Game X) : X → X → Prop where
  | here (x) : Desc g x x
  | next {x y z} : y ∈ g.children x → Desc g y z → Desc g x z

def colors := List.finRange 19
def potential {X} (g : Game X) (x : X) := sumBy colors fun c => val (g.shape x c)
def deficit {X} (g : Game X) (x : X) := sumBy colors fun c => (g.shape x c).length-1

private theorem finish {X} (g : Game X) (x : X) (d : Nat) (depth : g.left x = d)
    (valid : ∀ c, known (g.shape x c) = true) (low : potential g x < 2*fac d) :
    ∃ y, Desc g x y ∧ g.left y = 0 ∧ deficit g y ≤ 1 := by
  induction d generalizing x with
  | zero =>
    have eq : deficit g x = potential g x := by
      apply congrArg (sumBy colors)
      funext c
      exact (terminal (valid c) ((g.slots _ _).trans depth)).symm
    exact ⟨x,.here _,depth,by rw [eq]; change potential g x < 2 at low; omega⟩
  | succ d ih =>
    have pos : g.left x ≠ 0 := by omega
    have one (c : Fin 19) : ((g.children x).map (fun y => val (g.shape y c))).sum = val (g.shape x c) ∧
        ∀ y ∈ g.children x, known (g.shape y c) = true := by
      obtain ⟨a,ha,hp⟩ := g.outcomes x c pos
      obtain ⟨ok,eq⟩ := conditional (valid c) (by rwa [g.slots]) ha
      have hh := permSum (hp.map val)
      refine ⟨?_, fun y hy => List.all_eq_true.mp ok _ (hp.mem_iff.mp (List.mem_map_of_mem hy))⟩
      simpa [List.map_map, Function.comp_def, eq] using hh
    have conservation : sumBy (g.children x) (potential g) = potential g x := by
      unfold potential
      rw [transpose]
      apply congrArg (sumBy colors)
      funext c
      exact (one c).1
    have choose : ∃ y ∈ g.children x, potential g y < 2*fac d := by
      apply Classical.byContradiction
      intro no
      have floor := total_floor (g.children x) (f := potential g) (k := 2*fac d)
        (fun y hy => Nat.le_of_not_gt (fun lt => no ⟨y,hy,lt⟩))
      rw [conservation, g.count x pos, depth] at floor
      simp only [fac] at low
      rw [Nat.mul_left_comm] at low
      omega
    obtain ⟨y,hy,hlo⟩ := choose
    have dep := g.fewer x y hy
    obtain ⟨z,hz,hd,hval⟩ := ih y (by omega) (fun c => (one c).2 y hy) hlo
    exact ⟨z,.next hy hz,hd,hval⟩

/-- Nineteen arbitrary matchings may use completely different actions.
Some full placement has at most one extra connected component in total. -/
theorem at_most_one_extra_piece {X} (g : Game X) (root : X)
    (root_shape : ∀ c, g.shape root c = start) (depth : g.left root = 19) :
    ∃ y, Desc g root y ∧ g.left y = 0 ∧ deficit g y ≤ 1 := by
  apply finish g root 19 depth (fun c => by rw [root_shape]; exact initial.1)
  have eq : potential g root = sumBy colors (fun _ => 12760728035328000) := by
    unfold potential
    apply congrArg (sumBy colors)
    funext c
    rw [root_shape, initial.2.1]
  rw [eq]
  native_decide
#print axioms at_most_one_extra_piece
end K19Placement
