import UniversalLower
import Mathlib.Data.List.Dedup

namespace WildExact.SwitchFamily
open WildDeletion Finset
variable {n k : Nat} [NeZero n]

abbrev Edge (n : Nat) := Fin n × Fin n
abbrev Choice (n : Nat) := List (Edge n) × List (Edge n)
abbrev State (n : Nat) := Vector Nat n

def relabel (s : State n) (u v : Fin n) : State n :=
  s.map fun x => if x=s.get v then s.get u else x

def joinEdge (s : State n) (e : Edge n) : State n :=
  if s.get e.1 ≤ s.get e.2 then relabel s e.1 e.2 else relabel s e.2 e.1

def joined (s : State n) (es : List (Edge n)) := es.foldl joinEdge s

def doneState (s : State n) : Bool := (List.finRange n).all fun i => s.get i == s.get 0

def step (states : List (State n)) (choice : Choice n) : List (State n) :=
  ((states.flatMap fun s => [joined s choice.1,joined s choice.2]).filter (!doneState ·)).dedup

def initial (w : List (Edge n)) := joined (Vector.ofFn (fun x : Fin n => x.val)) w

def clears (w : List (Edge n)) (menu : List (Choice n)) : Bool :=
  ((menu.foldl step ([initial w].filter (!doneState ·)))).isEmpty

def Justified (E : Fin n → Fin n → Prop) (s : State n) : Prop :=
  ∀ x y, s.get x=s.get y → Walk E x y

omit [NeZero n] in
private theorem justified_relabel {E : Fin n → Fin n → Prop} (sym : ∀ {x y}, E x y → E y x)
    {s : State n} (ok : Justified E s) (u v : Fin n) (edge : E u v) : Justified E (relabel s u v) := by
  intro x y eq
  have tag (z : Fin n) : (relabel s u v).get z=(if s.get z=s.get v then s.get u else s.get z) :=
    Vector.getElem_map _ z.isLt
  rw [tag,tag] at eq
  by_cases xv : s.get x=s.get v <;> by_cases yv : s.get y=s.get v <;> simp [xv,yv] at eq
  · exact ok x y (xv.trans yv.symm)
  · exact ((ok x v xv).step (sym edge)).join (ok u y eq)
  · exact ((ok x u eq).step edge).join (ok v y yv.symm)
  · exact ok x y eq

omit [NeZero n] in
private theorem justified_joined {E : Fin n → Fin n → Prop} (sym : ∀ {x y}, E x y → E y x)
    {s : State n} (ok : Justified E s) (es : List (Edge n)) (has : ∀ e∈es,E e.1 e.2) :
    Justified E (joined s es) := by
  induction es generalizing s with
  | nil => exact ok
  | cons e es ih =>
    apply ih _ (fun l hl => has l (by simp [hl]))
    unfold joinEdge
    split
    · exact justified_relabel sym ok _ _ (has e (by simp))
    · exact justified_relabel sym ok _ _ (sym (has e (by simp)))

private theorem connected_done {E : Fin n → Fin n → Prop} {s : State n}
    (ok : Justified E s) (full : doneState s=true) : Connected E := by
  have same (i : Fin n) : s.get i=s.get 0 := eq_of_beq (List.all_eq_true.mp full i (List.mem_finRange _))
  exact fun x y => ok x y ((same x).trans (same y).symm)

def Available (E : Fin n → Fin n → Prop) (choice : Choice n) :=
  (∀ e∈choice.1,E e.1 e.2) ∨ (∀ e∈choice.2,E e.1 e.2)

private theorem fold_sound {E : Fin n → Fin n → Prop} (sym : ∀ {x y}, E x y → E y x)
    (menu : List (Choice n)) (avail : ∀ c∈menu, Available E c)
    (states : List (State n)) (empty : menu.foldl step states=[])
    (live : ∃ s∈states,Justified E s) : Connected E := by
  induction menu generalizing states with
  | nil =>
    change states=[] at empty
    simp [empty] at live
  | cons c rest ih =>
    obtain ⟨s,hs,ok⟩ := live
    have take (edges : List (Edge n)) (which : edges=c.1 ∨ edges=c.2)
        (yes : ∀ e∈edges,E e.1 e.2) : Connected E := by
      have good := justified_joined sym ok edges yes
      by_cases full : doneState (joined s edges)=true
      · exact connected_done good full
      apply ih (fun z hz => avail z (by simp [hz])) (step states c) empty
      refine ⟨joined s edges,?_,good⟩
      simp only [step,List.mem_dedup,List.mem_filter,List.mem_flatMap]
      refine ⟨⟨s,hs,by rcases which with rfl|rfl <;> simp⟩,by simpa using full⟩
    rcases avail c (by simp) with left|right
    · exact take c.1 (Or.inl rfl) left
    · exact take c.2 (Or.inr rfl) right

/-- Soundness for arbitrary edge choices, including simultaneous switches on several cycles. -/
theorem clears_sound {E : Fin n → Fin n → Prop} (sym : ∀ {x y}, E x y → E y x)
    (w : List (Edge n)) (menu : List (Choice n)) (hw : ∀ e∈w,E e.1 e.2)
    (available : ∀ c∈menu, Available E c) (pass : clears w menu=true) : Connected E := by
  have start : Justified E (initial w) := justified_joined sym
    (fun x y eq => (show Walk E x y from by
      have same : x=y := Fin.ext (by change (Vector.ofFn (fun i : Fin n => i.val))[x.val]=(Vector.ofFn (fun i : Fin n => i.val))[y.val] at eq; simpa using eq)
      rw [same]; exact .stay _)) w hw
  by_cases full : doneState (initial w)=true
  · exact connected_done start full
  apply fold_sound sym menu available _ (List.isEmpty_iff.mp pass)
  exact ⟨initial w,by simp [full],start⟩

structure Scheme (n k : Nat) where
  wild : List (Edge n)
  menu : Fin k → List (Choice n)

def Realizes (g : Coloring n k) (s : Scheme n k) :=
  ∀ c,∀ choice∈s.menu c,Available (fun x y => x≠y ∧ g.paint x y=c) choice

def checked (s : Scheme n k) (budget : Nat) : Bool :=
  s.wild.all (fun e => e.1<e.2) && s.wild.length≤budget &&
    (List.finRange k).all fun c => clears s.wild (s.menu c)

/-- A checked switch scheme supplies the same legal wild edges throughout its coloring family. -/
theorem upper_of_scheme (g : Coloring n k) (s : Scheme n k) (budget : Nat)
    (fit : Realizes g s) (yes : checked s budget=true) : Upper g budget := by
  obtain ⟨hw,hs⟩ := Bool.and_eq_true_iff.mp yes
  obtain ⟨hl,hc⟩ := Bool.and_eq_true_iff.mp hw
  refine ⟨s.wild.toFinset,fun e he => of_decide_eq_true (List.all_eq_true.mp hl e (List.mem_toFinset.mp he)),
    (List.toFinset_card_le _).trans (of_decide_eq_true hc),?_⟩
  intro c
  apply clears_sound (joined_symm g) s.wild (s.menu c) (fun e he => Or.inl (Or.inl (List.mem_toFinset.mpr he)))
    _ (List.all_eq_true.mp hs c (List.mem_finRange _))
  intro choice m
  exact (fit c choice m).imp (fun h e he => Or.inr (h e he)) (fun h e he => Or.inr (h e he))

end WildExact.SwitchFamily
