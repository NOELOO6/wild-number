import ExactModel
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
namespace WildExact
open Finset WildDeletion
variable {n k : Nat}
private def inc (e : Fin n × Fin n) (v : Fin n) := v = e.1 ∨ v = e.2
private instance (e : Fin n × Fin n) (v : Fin n) : Decidable (inc e v) :=
  inferInstanceAs (Decidable (_ ∨ _))
private def around (w : Lines n) (v : Fin n) := w.filter fun e => inc e v
private def weight (w : Lines n) (v : Fin n) := if (around w v).card = 1 then 2 else 1

private theorem confined {V : Type} {r : V → V → Prop} {a b} (s : V → Prop)
    (start : s a) (step : ∀ u v, s u → r u v → s v) (walk : Walk r a b) : s b := by
  induction walk with
  | stay => exact start
  | step _ edge ih => exact step _ _ ih edge

private theorem neighbor {a b x : Fin n} {w : Lines n} {e : Fin n × Fin n}
    (he : e ∈ w) (ea : inc e a) (ends : e = (a,b) ∨ e = (b,a))
    (one : (around w a).card = 1) (ax : Touch w a x) : x = b := by
  obtain ⟨only,ho⟩ := Finset.card_eq_one.mp one
  have same (d) (h : d ∈ around w a) : d = only := by simpa [ho] using h
  have eq := same e (Finset.mem_filter.mpr ⟨he,ea⟩)
  rcases ax with left|right
  · have e' := (same (a,x) (Finset.mem_filter.mpr ⟨left, Or.inl rfl⟩)).trans eq.symm
    rcases ends with hh|hh
    · exact congrArg Prod.snd (e'.trans hh)
    · have h := Prod.mk.inj (e'.trans hh); exact h.2.trans h.1
  · have e' := (same (x,a) (Finset.mem_filter.mpr ⟨right, Or.inr rfl⟩)).trans eq.symm
    rcases ends with hh|hh
    · have h := Prod.mk.inj (e'.trans hh); exact h.1.trans h.2
    · exact congrArg Prod.fst (e'.trans hh)

private theorem third (hn : 3 ≤ n) (a b : Fin n) : ∃ t : Fin n, t ≠ a ∧ t ≠ b := by
  classical
  by_contra! h
  have sub : (univ : Finset (Fin n)) ⊆ {a,b} := by
    intro v _
    by_cases x : v=a
    · simp [x]
    · simp [h v x]
  have bound := Finset.card_le_card sub
  have small := Finset.card_insert_le a ({b} : Finset (Fin n))
  simp only [card_univ,Fintype.card_fin,card_singleton] at bound small
  omega

private theorem pair_trap (hn : 3 ≤ n) (g : Coloring n k) (w : Lines n)
    (works : Works g w) {a b} (ab : a ≠ b)
    (left : ∀ v, Touch w a v → v = b) (right : ∀ v, Touch w b v → v = a) : False := by
  obtain ⟨t,ha,hb⟩ := third hn a b
  have closed (x y) (hx : x=a ∨ x=b) (h : Joined g w (g.paint a b) x y) : y=a ∨ y=b := by
    rcases hx with rfl|rfl
    · rcases h with e|⟨ne,col⟩
      · exact Or.inr (left _ e)
      · exact Or.inr (g.proper _ _ _ ne ab col)
    · rcases h with e|⟨ne,col⟩
      · exact Or.inl (right _ e)
      · exact Or.inl (g.proper _ _ _ ne ab.symm (col.trans (g.symm _ _)))
  exact (confined (fun v => v=a ∨ v=b) (Or.inl rfl) closed (works _ a t)).elim ha hb

private theorem zero_no_edge {a : Fin n} {w : Lines n} (h : (around w a).card=0) (v) :
    ¬ Touch w a v := by
  intro hv
  have no := Finset.card_eq_zero.mp h
  rcases hv with e|e
  · have mem : (a,v) ∈ around w a := Finset.mem_filter.mpr ⟨e,Or.inl rfl⟩
    simp [no] at mem
  · have mem : (v,a) ∈ around w a := Finset.mem_filter.mpr ⟨e,Or.inr rfl⟩
    simp [no] at mem

private def singles (w : Lines n) := univ.filter fun v => (around w v).card = 0

private theorem at_most_one (hn : 3 ≤ n) (g : Coloring n k) {w} (h : Works g w) :
    (singles w).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  by_contra diff
  have az := (Finset.mem_filter.mp ha).2
  have bz := (Finset.mem_filter.mp hb).2
  exact pair_trap hn g w h diff (fun v e => (zero_no_edge az v e).elim)
    (fun v e => (zero_no_edge bz v e).elim)

private theorem missing (g : Coloring n n) (v : Fin n) :
    ∃ c, ∀ u, v ≠ u → g.paint v u ≠ c := by
  classical
  let ns := (univ : Finset (Fin n)).erase v
  have le := Finset.card_image_le (s:=ns) (f:=g.paint v)
  have size : ns.card < n := by
    simp only [ns,card_erase_of_mem (mem_univ _),card_univ,Fintype.card_fin]
    have := v.isLt; omega
  have ne : ns.image (g.paint v) ≠ univ := by
    intro eq
    rw [eq,card_univ,Fintype.card_fin] at le
    omega
  have ex : ∃ c, c ∉ ns.image (g.paint v) := by
    by_contra! all
    exact ne (Finset.eq_univ_iff_forall.mpr all)
  obtain ⟨c,absent⟩ := ex
  refine ⟨c,fun u hu eq => absent (Finset.mem_image.mpr ⟨u,?_,eq⟩)⟩
  simp [ns,hu.symm]

private theorem all_touched (hn : 3 ≤ n) (g : Coloring n n) {w} (h : Works g w) :
    (singles w).card = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro v hv
  obtain ⟨c,miss⟩ := missing g v
  obtain ⟨z,ne,_⟩ := third hn v v
  have no := zero_no_edge (Finset.mem_filter.mp hv).2
  apply ne
  apply confined (fun u => u=v) rfl _ (h c v z)
  rintro _ u rfl (ew|⟨diff,eq⟩)
  · exact (no u ew).elim
  · exact (miss u diff eq).elim

private theorem account (hn : 3 ≤ n) (g : Coloring n k) {w} (legal : Legal w) (h : Works g w) :
    2*n ≤ 3*w.card + 2*(singles w).card := by
  classical
  let pay := fun v (e : Fin n × Fin n) => if inc e v then weight w v else 0
  have vertex (v : Fin n) : 2 ≤ (∑ e ∈ w, pay v e) + (if v ∈ singles w then 2 else 0) := by
    have cost : (∑ e ∈ w, pay v e) = (around w v).card * weight w v := by
      simp [pay,around,← Finset.sum_filter]
    rw [cost]
    by_cases hz : (around w v).card = 0
    · simp [singles,Finset.card_eq_zero.mp hz]
    · by_cases ho : (around w v).card=1 <;> simp [singles,hz,weight,ho]
      omega
  have line (e : Fin n × Fin n) (he : e ∈ w) : (∑ v, pay v e) ≤ 3 := by
    rcases e with ⟨a,b⟩
    have ne := (legal _ he).ne
    have split (v : Fin n) : pay v (a,b) =
        (if a=v then weight w a else 0) + (if b=v then weight w b else 0) := by
      by_cases x : a=v <;> by_cases y : b=v <;> simp_all [pay,inc,eq_comm]
    simp_rw [split,Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]
    by_cases ha : (around w a).card=1 <;> by_cases hb : (around w b).card=1
    · exact False.elim (pair_trap hn g w h ne
        (fun _ => neighbor he (Or.inl rfl) (Or.inl rfl) ha)
        (fun _ => neighbor he (Or.inr rfl) (Or.inr rfl) hb))
    all_goals simp [weight,ha,hb]
  have lo := Finset.sum_le_sum (s:=univ) (fun v _ => vertex v)
  have hi := Finset.sum_le_sum (s:=w) line
  rw [Finset.sum_add_distrib,Finset.sum_comm] at lo
  have idle : (∑ v : Fin n, if v∈singles w then 2 else 0) = 2*(singles w).card := by
    rw [← Finset.sum_filter]; simp [Nat.mul_comm]
  simp [idle,Nat.mul_comm] at lo hi
  omega

theorem odd_lower (hn : 3 ≤ n) (g : Coloring n n) {w} (legal : Legal w) (h : Works g w) :
    (2*n+2)/3 ≤ w.card := by
  have hi := account hn g legal h
  rw [all_touched hn g h] at hi
  omega

theorem even_lower (hn : 3 ≤ n+1) (g : Coloring (n+1) n) {w} (legal : Legal w) (h : Works g w) :
    (2*n+2)/3 ≤ w.card := by
  have hi := account hn g legal h
  have lo := at_most_one hn g h
  omega

theorem exact_of_upper {g : Coloring n k} {b} (upper : Upper g b)
    (lower : ∀ w, Legal w → Works g w → b ≤ w.card) : Exact g b := by
  obtain ⟨w,leg,bound,win⟩ := upper
  exact ⟨⟨w,leg,Nat.le_antisymm bound (lower w leg win),win⟩, lower⟩

theorem exact_pair {n} (hn : 3 ≤ n) (upper : ∀ g : Coloring n n, Upper g ((2*n+2)/3)) :
    (∀ g : Coloring n n, Exact g ((2*n+2)/3)) ∧
    (∀ g : Coloring (n+1) n, Exact g ((2*n+2)/3)) :=
  ⟨fun g => exact_of_upper (upper g) (fun _ => odd_lower hn g),
   fun g => exact_of_upper (even_upper upper g) (fun _ => even_lower (by omega) g)⟩
#print axioms exact_pair
end WildExact
