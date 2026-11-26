import Delete
namespace K17Connectivity
open WildDeletion

abbrev V := Fin 18
abbrev B := Fin 6
def blocks : List B := [0,1,2,3,4,5]
def extra : List B := [1,1,2,3,4,5]
def ends {α : Type} (edges : List (α × α)) := edges.flatMap fun (x,y) => [x,y]
/-- One point per block, then extra pairs, gives sizes 1,5,3,3,3,3. -/
def labels := blocks ++ ends (extra.map fun x => (x,x))

private theorem count_ends {α : Type} (p : α → Bool) (es : List (α × α))
    (closed : ∀ e ∈ es, p e.1 = p e.2) :
    ((ends es).filter p).length = 2*(es.filter (fun e => p e.1)).length := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    have h := closed e (by simp)
    have t := ih (fun f hf => closed f (by simp [hf]))
    cases e with
    | mk x y =>
      change p x = p y at h
      cases hx : p x <;> simp [ends, List.filter_cons, hx, h.symm, ends] at t ⊢ <;> omega

private theorem complement_count {α : Type} (p : α → Bool) (l : List α) :
    (l.filter p).length + (l.filter (fun v => !p v)).length = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih => cases hx : p x <;> simp [List.filter_cons, hx] <;> omega

private theorem layout_parity (keep : B → Bool) :
    (labels.filter keep).length % 2 = (blocks.filter keep).length % 2 := by
  have h := count_ends keep (extra.map fun x => (x,x)) (by
    intro e he; obtain ⟨x,_,rfl⟩ := List.mem_map.mp he; rfl)
  simp only [labels, List.filter_append, List.length_append]
  omega

/-- For any eighteen-point matching and any connected wild blocks of the
    indicated sizes, crossing every two-block cut implies path connectivity. -/
theorem fifteen_cuts_suffice (E : V → V → Prop) (owner : V → B) (rep : B → V)
    (shape : ((List.finRange 18).map owner).Perm labels)
    (inside : ∀ x, Walk E x (rep (owner x)) ∧ Walk E (rep (owner x)) x)
    (colors : List (V × V)) (perfect : (ends colors).Perm (List.finRange 18))
    (drawn : ∀ e ∈ colors, E e.1 e.2 ∧ E e.2 e.1)
    (cuts : ∀ keep : B → Bool, (blocks.filter keep).length = 2 →
      ∃ e ∈ colors, keep (owner e.1) ≠ keep (owner e.2)) : Connected E := by
  classical
  intro s t
  apply Classical.byContradiction
  intro noPath
  let keep (b : B) := decide (Walk E s (rep b))
  let mark (x : V) := keep (owner x)
  have iffReach (x : V) : mark x = true ↔ Walk E s x := by
    change decide (Walk E s (rep (owner x))) = true ↔ _
    rw [decide_eq_true_eq]
    exact ⟨fun h => h.join (inside x).2, fun h => h.join (inside x).1⟩
  have closed : ∀ e ∈ colors, mark e.1 = mark e.2 := by
    intro e he
    apply Bool.eq_iff_iff.mpr
    rw [iffReach, iffReach]
    exact ⟨fun h => .step h (drawn e he).1, fun h => .step h (drawn e he).2⟩
  have fromEdges := count_ends mark colors closed
  have cover := (perfect.filter mark).length_eq
  have fromBlocks := (shape.filter keep).length_eq
  simp only [List.filter_map, List.length_map] at fromBlocks
  change ((List.finRange 18).filter mark).length = (labels.filter keep).length at fromBlocks
  have parity := layout_parity keep
  have every : ∀ x : B, x ∈ blocks := by decide
  have start : keep (owner s) = true := (iffReach s).mpr (.stay _)
  have finish : keep (owner t) = false := by
    cases h : keep (owner t) with
    | false => rfl
    | true => exact False.elim (noPath ((iffReach t).mp h))
  have nonempty : 0 < (blocks.filter keep).length :=
    List.length_filter_pos_iff.mpr ⟨owner s,every _,start⟩
  have proper : 0 < (blocks.filter (fun b => !keep b)).length :=
    List.length_filter_pos_iff.mpr ⟨owner t,every _,by simp [finish]⟩
  have six := complement_count keep blocks
  have size : blocks.length = 6 := by decide
  have sides : (blocks.filter keep).length = 2 ∨
      (blocks.filter (fun b => !keep b)).length = 2 := by omega
  rcases sides with small | small
  · obtain ⟨e,he,cross⟩ := cuts keep small
    exact cross (closed e he)
  · obtain ⟨e,he,cross⟩ := cuts (fun b => !keep b) small
    exact cross (congrArg Bool.not (closed e he))

#print axioms fifteen_cuts_suffice
end K17Connectivity
