import Bounds
namespace K19Exchange
open EdgeWalk WildDeletion Finset
abbrev V := Fin 19
abbrev E := Edge 19
def table : Array (List E) := #[
  [(2,10),(1,7),(5,6),(14,15),(3,13),(8,9),(0,4),(11,12),(16,17)],
  [(7,16),(9,10),(11,15),(3,5),(0,13),(12,18),(1,4),(14,17),(2,6)],
  [(6,9),(2,7),(3,14),(10,11),(0,16),(4,5),(1,12),(8,15),(17,18)],
  [(7,18),(8,16),(3,10),(0,14),(1,6),(4,17),(2,13),(5,11),(12,15)],
  [(9,15),(1,17),(11,13),(2,8),(3,7),(6,14),(12,16),(4,10),(0,18)],
  [(4,18),(7,15),(6,16),(11,14),(3,9),(0,5),(2,17),(8,12),(1,13)],
  [(1,18),(5,10),(3,6),(8,14),(9,12),(0,17),(4,11),(2,16),(13,15)],
  [(2,15),(1,5),(9,11),(3,17),(14,16),(6,12),(4,7),(8,10),(13,18)],
  [(5,18),(10,14),(7,12),(6,8),(3,11),(9,16),(0,15),(13,17),(1,2)],
  [(1,8),(15,16),(6,10),(0,2),(4,14),(5,9),(7,13),(12,17),(11,18)],
  [(7,9),(8,18),(0,3),(1,14),(6,17),(4,13),(2,11),(5,15),(10,12)],
  [(0,6),(7,17),(8,11),(3,18),(1,16),(9,13),(5,14),(2,4),(10,15)],
  [(3,15),(13,16),(2,9),(0,8),(1,11),(4,12),(5,17),(7,14),(10,18)],
  [(11,16),(3,8),(6,15),(1,10),(2,18),(4,9),(13,14),(5,7),(0,12)],
  [(9,18),(1,15),(11,17),(8,13),(2,3),(6,7),(5,12),(4,16),(0,10)],
  [(14,18),(7,10),(6,11),(1,3),(0,9),(15,17),(5,16),(12,13),(4,8)],
  [(2,5),(0,11),(9,17),(3,16),(12,14),(4,6),(7,8),(10,13),(15,18)],
  [(6,18),(0,7),(8,17),(3,12),(10,16),(1,9),(5,13),(2,14),(4,15)],
  [(0,1),(16,18),(10,17),(7,11),(6,13),(3,4),(2,12),(9,14),(5,8)]]
def color (c : V) := table[c.val]!
def start : List E := [(0,1),(0,2),(0,3),(4,5),(4,6),(7,8),(7,9),(10,11),(10,12),(13,14),(13,15),(16,17),(16,18)]
def finish : List E := [(0,2),(0,3),(4,5),(4,6),(7,8),(7,9),(10,11),(10,12),(13,14),(13,15),(16,18),(0,17),(1,16)]

def drawing : WildLower.Coloring V where
  edges := color
  missing := by unfold Adj; native_decide
  proper := by unfold Adj; native_decide
  complete := by unfold Adj; native_decide

theorem legal : start.Nodup ∧ finish.Nodup ∧ start.length = 13 ∧ finish.length = 13 ∧
    (∀ e ∈ start, e.1 < e.2) ∧ (∀ e ∈ finish, e.1 < e.2) ∧
    start.toFinset \ finish.toFinset = {(0,1),(16,17)} ∧
    finish.toFinset \ start.toFinset = {(0,17),(1,16)} := by native_decide

theorem start_paths (c : V) (h : c ≠ 0) : Connected (Adj (start ++ color c)) := by
  have all : ∀ i : V, i ≠ 0 → passes 0 (start ++ color i) = true := by native_decide
  exact connected_of_passes _ _ (all c h)
theorem finish_paths (c : V) : Connected (Adj (finish ++ color c)) := by
  have all : ∀ i : V, passes 0 (finish ++ color i) = true := by native_decide
  exact connected_of_passes _ _ (all c)

def side (v : V) : Bool := v.val < 16

private theorem same_on_walk {n : Nat} {es : List (Edge n)} (f : Fin n → Bool)
    (closed : ∀ e ∈ es, f e.1 = f e.2) {x y} (h : Walk (Adj es) x y) : f x = f y := by
  induction h with
  | stay => rfl
  | step _ he ih => exact ih.trans (he.elim (fun q => closed _ q) (fun q => (closed _ q).symm))

theorem last_two (x y : V) : Walk (Adj (start ++ color 0)) x y ↔ side x = side y := by
  constructor
  · exact same_on_walk side (by native_decide)
  · intro eq
    have h : ∀ u v : V, side u = side v →
        (run (start ++ color 0) 19 (2^u.val)).testBit v.val = true := by native_decide
    exact walk_of_seen _ _ _ (h x y eq)

def witness (es : List E) (s : Nat) := s.testBit 0 &&
  (List.finRange 19).any (fun v => !s.testBit v.val) &&
  es.all (fun e => s.testBit e.1.val == s.testBit e.2.val)
def rejects (w : List E) := (List.finRange 19).any fun c =>
  let es := w ++ color c
  witness es (run es 19 1)

theorem rejected (w : List E) (h : rejects w = true) : ¬ ∀ c, Connected (Adj (w ++ color c)) := by
  intro paths
  obtain ⟨c,_,hc⟩ := List.any_eq_true.mp h
  let es := w ++ color c
  let s := run es 19 1
  have z : ((s.testBit 0 && (List.finRange 19).any (fun v => !s.testBit v.val)) &&
      es.all (fun e => s.testBit e.1.val == s.testBit e.2.val)) = true := hc
  obtain ⟨b,d⟩ := Bool.and_eq_true_iff.mp z
  obtain ⟨one,absent⟩ := Bool.and_eq_true_iff.mp b
  obtain ⟨v,_,hv⟩ := List.any_eq_true.mp absent
  have wall := same_on_walk (fun x : V => s.testBit x.val)
    (fun e he => beq_iff_eq.mp (List.all_eq_true.mp d _ he)) (paths c 0 v)
  simp [one] at wall
  simp [wall] at hv

end K19Exchange
