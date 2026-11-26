import GraphLayouts
namespace WildCuts
open Finset WildDeletion EdgeWalk

def ordered {n : Nat} (e : Edge n) := if e.1 ≤ e.2 then e else e.swap
noncomputable def tidy {n : Nat} (es : List (Edge n)) := ((es.map ordered).toFinset).toList

theorem tidy_properties {n : Nat} (es : List (Edge n)) (ne : ∀ e ∈ es, e.1 ≠ e.2) :
    (tidy es).length ≤ es.length ∧ (tidy es).Nodup ∧ ∀ e ∈ tidy es, e.1 < e.2 := by
  refine ⟨?_,Finset.nodup_toList _,?_⟩
  · simpa [tidy] using (es.map ordered).toFinset_card_le
  · intro e he
    have mem : e ∈ es.map ordered := by simpa [tidy] using he
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp mem
    have h := ne x hx
    unfold ordered
    split
    · exact lt_of_le_of_ne ‹_› h
    · exact lt_of_not_ge ‹_›

theorem tidy_connected {n : Nat} (es m : List (Edge n)) (h : Connected (Adj (es++m))) :
    Connected (Adj (tidy es ++ m)) := by
  have keep {a b : Fin n} (he : (a,b) ∈ es) : Adj (tidy es) a b := by
    have present : ordered (a,b) ∈ tidy es := by simpa [tidy] using List.mem_map_of_mem (f := ordered) he
    by_cases le : a ≤ b
    · exact Or.inl (by simpa [ordered,le] using present)
    · exact Or.inr (by simpa [ordered,le] using present)
  have lift {a b : Fin n} (he : (a,b) ∈ es++m) : Adj (tidy es++m) a b := by
    rcases List.mem_append.mp he with old | col
    · rcases keep old with q | q
      · exact Or.inl (List.mem_append_left _ q)
      · exact Or.inr (List.mem_append_left _ q)
    · exact Or.inl (List.mem_append_right _ col)
  intro a b
  apply Walk.mapInto id (E := Adj (es++m)) _ (h a b)
  intro x y e
  exact Walk.step (.stay _) (e.elim (fun t => lift t) (fun t => (lift t).symm))

theorem wild_simple {n : Nat} {G : Type} (b : Blocks (Fin n) G) (p : Equiv.Perm (Fin n))
    (e : Edge n) (he : e ∈ wild b p) : e.1 ≠ e.2 := by
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp he
  apply p.injective.ne
  simpa using (List.mem_filter.mp hx).2

end WildCuts
