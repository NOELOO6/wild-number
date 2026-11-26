import Bounds
namespace WildMenu
open WildCuts EdgeWalk WildDeletion Finset
abbrev V := Fin 19
abbrev G := Fin 6
abbrev Key := Nat × Nat

/-- Choose the smaller side. Nineteen is odd, so no tie is possible. -/
def smaller (s : Finset V) := if s.card ≤ 9 then s else sᶜ
def cut (i : Fin 31) := smaller (univ.filter fun x : V => (i.val+1).testBit (groups19.tag x).val)
def key (s : Finset V) : Key := (s.card, ∑ x ∈ s, 2^x.val)

theorem cut_names : ∀ u : SideName G 5, ∃ i : Fin 31,
    cut i = smaller (side groups19 u.1) := by decide +kernel

private theorem map_smaller (s : Finset V) (p : Equiv.Perm V) :
    (smaller s).map p.toEmbedding = smaller (s.map p.toEmbedding) := by
  classical
  by_cases h : s.card ≤ 9
  · simp [smaller,h]
  · simp only [smaller,Finset.card_map,if_neg h]
    ext x
    simp [Finset.mem_map_equiv]

def closedSides (q : Equiv.Perm V) := fun j : Finset (Fin 10) =>
  (side (pairs 19) j).map q.toEmbedding

private theorem labelSide {H : Type} [Fintype H] [DecidableEq H]
    (b : Blocks V H) (p : Equiv.Perm V) (s : Finset V)
    (h : ∀ x, p x ∈ s ↔ p (b.rep (b.tag x)) ∈ s) :
    (side b (univ.filter fun g => p (b.rep g) ∈ s)).map p.toEmbedding = s := by
  ext v
  rw [Finset.mem_map_equiv]
  simpa [side] using (h (p.symm v)).symm

theorem survivor (p q : Equiv.Perm V) (m : List (Edge 19))
    (colored : ∀ x, x ≠ (pairs 19).rep ((pairs 19).tag x) →
      Adj m (q x) (q ((pairs 19).rep ((pairs 19).tag x))))
    (avoids : ∀ (i : Fin 31) (j : Finset (Fin 10)),
      key ((cut i).map p.toEmbedding) ≠ key (closedSides q j)) :
    Connected (Adj (wild groups19 p ++ m)) := by
  classical
  let E := Adj (wild groups19 p ++ m)
  let r := p (groups19.rep 5)
  have rev {a b : V} (h : Walk E a b) : Walk E b a := by
    induction h with
    | stay => exact .stay _
    | step _ e ih => exact (Walk.step (E := E) (.stay _) e.symm).join ih
  have reach (v : V) : Walk E r v := by
    by_contra hv
    let A := univ.filter (fun x => ¬ Walk E r x)
    have mem (x : V) : x ∈ A ↔ ¬ Walk E r x := by simp [A]
    have inv (x y : V) (e : E x y) : x ∈ A ↔ y ∈ A := by
      rw [mem,mem]
      exact not_congr ⟨fun h => .step h e,fun h => .step h e.symm⟩
    have left (x : V) : p x ∈ A ↔ p (groups19.rep (groups19.tag x)) ∈ A := by
      by_cases eq : x = groups19.rep (groups19.tag x)
      · rw [← eq]
      apply inv
      rcases wild_step groups19 p x eq with h | h
      · exact Or.inl (List.mem_append_left _ h)
      · exact Or.inr (List.mem_append_left _ h)
    let u := univ.filter (fun j => p (groups19.rep j) ∈ A)
    have hu : u.Nonempty := by
      refine ⟨groups19.tag (p.symm v),Finset.mem_filter.mpr ⟨Finset.mem_univ _,(left _).mp ?_⟩⟩
      simpa using (mem v).mpr hv
    have hr : (5 : G) ∉ u := by
      intro h
      exact (mem r).1 (Finset.mem_filter.mp h).2 (.stay r)
    obtain ⟨i,hi⟩ := cut_names ⟨u,hu,hr⟩
    have li : (cut i).map p.toEmbedding = smaller A := by
      rw [hi,map_smaller,labelSide groups19 p A left]
    have right (x : V) : q x ∈ smaller A ↔ q ((pairs 19).rep ((pairs 19).tag x)) ∈ smaller A := by
      by_cases eq : x = (pairs 19).rep ((pairs 19).tag x)
      · rw [← eq]
      have pair : E (q x) (q ((pairs 19).rep ((pairs 19).tag x))) := by
        rcases colored x eq with h | h
        · exact Or.inl (List.mem_append_right _ h)
        · exact Or.inr (List.mem_append_right _ h)
      have h := inv _ _ pair
      unfold smaller
      split
      · exact h
      · simpa using not_congr h
    exact avoids i _ (congrArg key (li.trans (labelSide (pairs 19) q (smaller A) right).symm))
  exact fun x y => (rev (reach x)).join (reach y)
end WildMenu
