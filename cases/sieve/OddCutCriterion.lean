import FilteredMoments
import UniversalLower
import StarDraw

namespace WildSieve.FilteredCuts
open Finset WildExact WildDeletion
variable {n k : Nat}

/-- No edge of a specified color crosses this side. -/
def closedSide (g : Coloring n k) (c : Fin k) (S : Finset (Fin n)) :=
  ∀ x∈S,∀ y∉S,g.paint x y≠c

private theorem closed_compl (g : Coloring n k) (c : Fin k) (S : Finset (Fin n))
    (h : closedSide g c S) : closedSide g c Sᶜ := by
  intro x hx y hy col
  exact h y (by simpa using hy) x (mem_compl.mp hx) ((g.symm y x).trans col)

noncomputable def singleCuts (g : Coloring n k) : Finset (Finset (Fin n)) := by
  classical exact univ.filter (fun S => S.card=3 ∧ ∃ c,closedSide g c S)

/-- All cuts still possible after excluding individual triples. -/
noncomputable def largerCuts (g : Coloring n k) : Finset (Finset (Fin n)) := by
  classical exact univ.filter (fun S => 6≤S.card ∧ 2*S.card≤n ∧ S.card%3=0 ∧ ∃ c,closedSide g c S)

/-- On fifteen vertices the remaining cuts are exactly the six-vertex sides closed by a color. -/
theorem fifteen_cuts (g : Coloring 15 k) (S : Finset (Fin 15)) :
    S∈largerCuts g ↔ S.card=6 ∧ ∃ c,closedSide g c S := by
  classical simp only [largerCuts,mem_filter,mem_univ,true_and]
  constructor
  · rintro ⟨a,b,d,c⟩; exact ⟨by omega,c⟩
  · rintro ⟨a,c⟩; exact ⟨by omega,by omega,by omega,c⟩

/-- The reduction works for every triple order and every number of colors. -/
theorem upper_from_survivor (g : Coloring n k) (t : Nat) (order : n=3*t)
    (L : Layout (univ : Finset (Fin n))) (pass : L∈survivors (singleCuts g) (largerCuts g) univ) :
    Upper g (2*t) := by
  classical
  obtain ⟨clean,rest⟩ := mem_sdiff.mp pass
  let w := L.val.biUnion spokes
  have num := L.property.1.card_vertices
  rw [L.property.2,card_univ,Fintype.card_fin] at num
  have count : L.val.card=t := by omega
  refine ⟨w,?_,?_,?_⟩
  · intro e he
    obtain ⟨T,_,h⟩ := mem_biUnion.mp he
    exact spokes_legal T e h
  · apply card_biUnion_le.trans
    calc
      _ ≤ ∑ _∈L.val,2 := sum_le_sum fun T h => (spokes_bound T).trans (by rw [L.property.1.size _ h])
      _ = _ := by simp [count,Nat.mul_comm]
  intro c x y
  by_contra lost
  let S := univ.filter fun v => Walk (Joined g w c) x v
  have inside (v) : v∈S ↔ Walk (Joined g w c) x v := by simp [S]
  have sealed : closedSide g c S := by
    intro a ha b hb edge
    exact hb ((inside b).mpr (.step ((inside a).mp ha) (Or.inr ⟨fun eq => hb (eq ▸ ha),edge⟩)))
  have respect (b) (hb : b∈L.val) : b⊆S ∨ Disjoint b S := by
    by_cases dis : Disjoint b S
    · exact Or.inr dis
    obtain ⟨v,hv,vs⟩ := not_disjoint_iff.mp dis
    refine Or.inl (fun z hz => (inside z).mpr (((inside v).mp vs).join ?_))
    apply Walk.mapInto (E:=Touch w) id (fun _ _ h => .step (.stay _) (Or.inl h))
    exact in_star (fun e he => mem_biUnion.mpr ⟨b,hb,he⟩) hv hz
  have obstruction (A : Finset (Fin n)) (pos : A.Nonempty) (small : 2*A.card≤n)
      (cl : closedSide g c A) (whole : ∀ b∈L.val,b⊆A ∨ Disjoint b A) : False := by
    have event : L∈localSeal univ A := (seal_whole (subset_univ _) L).mpr (by
      intro b hb v hv va
      exact (whole b hb).resolve_right (fun d => disjoint_left.mp d hv va))
    obtain ⟨M,sub⟩ := local_seal_mem.mp event
    have sz := M.property.1.card_vertices
    rw [M.property.2] at sz
    have ne := card_pos.mpr pos
    by_cases one : A.card=3
    · have cm : M.val.card=1 := by omega
      obtain ⟨b,eq⟩ := card_eq_one.mp cm
      have bA : b=A := by simpa [vertices,eq] using M.property.2
      have bL : b∈L.val := sub (by simp [eq])
      exact (mem_layouts.mp clean b bL).1 (by simp only [singleCuts,mem_filter,mem_univ,true_and,bA]; exact ⟨one,c,cl⟩)
    · apply rest (mem_biUnion.mpr ⟨A,by simp only [largerCuts,mem_filter,mem_univ,true_and];
                                         exact ⟨by omega,small,by omega,c,cl⟩,?_⟩)
      exact mem_layouts.mpr (fun b hb => ⟨(mem_layouts.mp clean b hb).1,fun Q hQ => mem_singleton.mp hQ ▸ whole b hb⟩)
  by_cases small : 2*S.card≤n
  · exact obstruction S ⟨x,(inside x).mpr (.stay _)⟩ small sealed respect
  · apply obstruction Sᶜ ⟨y,mem_compl.mpr (fun h => lost ((inside y).mp h))⟩
    · rw [card_compl,Fintype.card_fin]; omega
    · exact closed_compl g c S sealed
    · intro b hb
      rcases respect b hb with inc|dis
      · exact Or.inr (disjoint_left.mpr fun _ h z => mem_compl.mp z (inc h))
      · exact Or.inl (fun _ h => mem_compl.mpr (disjoint_left.mp dis h))

/-- Either cubic inequality can certify an unrestricted coloring without supplying a layout. -/
theorem exact_of_moments (g : Coloring n n) (t : Nat) (order : n=3*t) (lo : 3≤n)
    (test : let H := singleCuts g; let K := largerCuts g; let U : Finset (Fin n) := univ
      6*first H K U+third H K U<6*count H U []+3*second H K U ∨
      12*first H K U+third H K U<12*count H U []+5*second H K U) : Exact g (2*t) := by
  classical
  let H := singleCuts g
  let K := largerCuts g
  let U : Finset (Fin n) := univ
  have positive : 0<(survivors H K U).card := by
    rcases test with a|b
    · have z := cubic H K U; change _ < _ at a; dsimp only [H,K,U] at *; omega
    · have z := cubic_twelve H K U; dsimp only [H,K,U] at *; omega
  obtain ⟨L,pass⟩ := card_pos.mp positive
  exact exact_of_upper (upper_from_survivor g t order L pass) (fun w leg works => by
    have h := odd_lower lo g leg works; omega)

#print axioms exact_of_moments
end WildSieve.FilteredCuts
