import SixBoundary

namespace BoundaryOptions
open VertexRedraw EdgeWalk WildDeletion
open SixBoundary (ref)

def fixedAt (locked : V → V → Bool) (c : C) (x : V) := locked x (ref c x)
def knownPairs (locked : V → V → Bool) (c : C) : R := points.filterMap fun x =>
  if fixedAt locked c x && decide (x < ref c x) then some (x,ref c x) else none
def free (locked : V → V → Bool) (c : C) := points.filter fun x => !fixedAt locked c x
def allowed (locked : V → V → Bool) (c : C) (e : Edge 16) := !locked e.1 e.2 || ref c e.1 == e.2
def possible (locked : V → V → Bool) (c : C) := ((fills 16 (free locked c)).filter (fun m => m.all (allowed locked c))).map (knownPairs locked c ++ ·)

theorem represented (locked : V → V → Bool)
    (stable : ∀ d x, fixedAt locked d (ref d x) = fixedAt locked d x) (f : C → V → V) (inv : ∀ c x, f c (f c x) = x)
    (ne : ∀ c x, f c x ≠ x) (proper : ∀ c d, c≠d → ∀ x, f c x ≠ f d x)
    (agree : ∀ c x, fixedAt locked c x = true → f c x = ref c x) (c : C) :
    ∃ m ∈ possible locked c, respects (f c) m := by
  have mem : ∀ x : V, x ∈ points := by decide
  have cover : ∀ x y : V, x ≠ y → colors.any (fun d => ref d x == y) = true := by native_decide
  have closed (x : V) (hx : x ∈ free locked c) : f c x ∈ free locked c := by
    have no : fixedAt locked c x = false := by simpa [free] using (List.mem_filter.mp hx).2
    apply List.mem_filter.mpr
    refine ⟨mem _,?_⟩
    cases flag : fixedAt locked c (f c x) with
    | false => rfl
    | true =>
      have eq := agree c _ flag
      rw [inv] at eq
      have contra := stable c (f c x)
      rw [←eq,no,flag] at contra
      contradiction
  have len (d : C) : (free locked d).length ≤ 16 := Nat.le_trans (List.length_filter_le ..) (by decide : points.length ≤ 16)
  obtain ⟨m,hm,ok⟩ := fills_complete _ (inv c) (ne c) 16 _ (len c) closed
  have allowedAll : m.all (allowed locked c) = true := by
    apply List.all_eq_true.mpr
    intro e he
    have fc := ok e he
    cases lock : locked e.1 e.2 with
    | false => simp [allowed,lock]
    | true =>
      have diff : e.1 ≠ e.2 := fun h => ne c _ (fc.trans h.symm)
      obtain ⟨d,_,test⟩ := List.any_eq_true.mp (cover _ _ diff)
      have hd : ref d e.1 = e.2 := by simpa using test
      have eq := agree d e.1 (by simpa only [fixedAt,hd] using lock)
      have same : c = d := by
        apply Classical.byContradiction
        intro h
        exact proper c d h _ (fc.trans (eq.trans hd).symm)
      subst d
      simp [allowed,hd]
  refine ⟨_,List.mem_map.mpr ⟨m,List.mem_filter.mpr ⟨hm,allowedAll⟩,rfl⟩,?_⟩
  intro e he
  rcases List.mem_append.mp he with old|new
  · obtain ⟨x,_,ev⟩ := List.mem_filterMap.mp old
    split at ev
    · cases ev
      exact agree _ _ (Bool.and_eq_true_iff.mp (by assumption)).1
    · contradiction
  · exact ok _ new

end BoundaryOptions
