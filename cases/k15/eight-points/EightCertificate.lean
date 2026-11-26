import EightPoints
namespace EightPoints
open EdgeWalk WildDeletion
set_option interpreter.prefer_native true
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem seventy : layouts.length = 70 ∧ layouts.Nodup ∧ layouts.all (fun w => w.length == 10) = true := by native_decide
theorem concrete_costs : patterns.map cost = [8,0,8,0,0,4,8,4,0,4,0,8,0,8,8] := by native_decide
private theorem le_ceiling {n : Nat} {ns : List Nat} (h : n ∈ ns) : n ≤ ceiling ns := by
  induction ns with
  | nil => contradiction
  | cons a ns ih =>
    rcases List.mem_cons.mp h with rfl | ht
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih ht) (Nat.le_max_right _ _)

private theorem intersect {α} (ls : List α) (p q : α → Bool) :
    (ls.filter q).length ≤ (ls.filter (fun w => p w && q w)).length +
      (ls.filter fun w => !(p w)).length := by
  induction ls with
  | nil => simp
  | cons x xs ih => cases hp : p x <;> cases hq : q x <;>
      simp [List.filter_cons,hp,hq] at ih ⊢ <;> omega

/-- A test on any prescribed local table. The other 84 lines may vary. -/
theorem completion_bound (cs : List (Raw × Raw))
    (allowed : ∀ c ∈ cs, c.2 ∈ completions c.1) :
    layouts.length ≤ (surviving cs).length + spent cs := by
  induction cs with
  | nil =>
    change layouts.length ≤ (layouts.filter (fun _ => true)).length + 0
    rw [List.filter_eq_self.mpr (fun _ _ => rfl)]
    omega
  | cons c cs ih =>
    have old := ih (fun t ht => allowed t (by simp [ht]))
    have budget : failures c.2 ≤ cost c.1 := le_ceiling (List.mem_map_of_mem (allowed c (by simp)))
    have loss := intersect layouts (safe c.2) (working cs)
    change layouts.length ≤ (surviving (c::cs)).length + (cost c.1 + spent cs)
    have join : surviving (c::cs) = layouts.filter (fun w => safe c.2 w && working cs w) := by rfl
    rw [join]
    unfold surviving at old
    unfold failures at budget
    omega

theorem genuine_paths (cs : List (Raw × Raw)) {w : Edges} (h : w ∈ surviving cs) :
    w.length = 10 ∧ ∀ c ∈ cs, Connected (Adj (w ++ withoutRoot c.2)) := by
  obtain ⟨hw,ok⟩ := List.mem_filter.mp h
  exact ⟨beq_iff_eq.mp (List.all_eq_true.mp seventy.2.2 _ hw),
    fun c hc => connected_of_passes 0 _ (List.all_eq_true.mp ok _ hc)⟩

theorem ten_survive_every_completion (cs : List (Raw × Raw)) (table : cs.map Prod.fst = patterns)
    (allowed : ∀ c ∈ cs, c.2 ∈ completions c.1) :
    10 ≤ (surviving cs).length ∧ (surviving cs).Nodup ∧
      ∀ w ∈ surviving cs, w.length = 10 ∧ ∀ c ∈ cs, Connected (Adj (w ++ withoutRoot c.2)) := by
  have b := completion_bound cs allowed
  have paid : spent cs = 60 := by
    change (cs.map (fun c => cost c.1)).sum = 60
    rw [show cs.map (fun c => cost c.1) = (cs.map Prod.fst).map cost by simp only [List.map_map, Function.comp_def],
        table,concrete_costs]
    decide
  exact ⟨by rw [seventy.1,paid] at b; omega, seventy.2.1.filter _,fun _ h => genuine_paths cs h⟩
#print axioms ten_survive_every_completion
end EightPoints
