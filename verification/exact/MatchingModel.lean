import UniversalLower
namespace WildExact
open Finset WildDeletion
variable {n : Nat}
def Absent (g : Coloring n n) (v c : Fin n) := ∀ u, v ≠ u → g.paint v u ≠ c

theorem unique_missing (g : Coloring n n) (v : Fin n) : ∃! c, Absent g v c := by
  classical
  let used := ((univ : Finset (Fin n)).erase v).image (g.paint v)
  have hu : used.card = n-1 := by
    rw [Finset.card_image_of_injOn]
    · simp
    · intro x hx y hy eq
      exact g.proper _ _ _ (Finset.mem_erase.mp hx).1.symm (Finset.mem_erase.mp hy).1.symm eq
  have hc : usedᶜ.card = 1 := by
    rw [Finset.card_compl,hu,Fintype.card_fin]
    have := v.isLt; omega
  have iff (c : Fin n) : c∈usedᶜ ↔ Absent g v c := by
    simp [used,Absent,Finset.mem_image,eq_comm]
  obtain ⟨c,one⟩ := Finset.card_eq_one.mp hc
  refine ⟨c,(iff c).mp (by simp [one]),fun y h => ?_⟩
  simpa [one] using (iff y).mpr h

/-- A fixed-point-free pairing would make the number of ordinary vertices even. -/
theorem missing_somewhere (hn : n%2=1) (g : Coloring n n) (c : Fin n) :
    ∃ v, Absent g v c := by
  classical
  by_contra! none
  have paired (v : Fin n) : ∃ u, v ≠ u ∧ g.paint v u=c := by
    by_contra! no
    exact none v no
  choose f hfne hfc using paired
  have inv (v) : f (f v)=v :=
    g.proper _ _ _ (hfne _) (hfne _).symm ((hfc _).trans ((g.symm _ _).trans (hfc v)).symm)
  let low := univ.filter (fun v => v < f v)
  let hi := univ.filter (fun v => f v < v)
  have image : low.image f = hi := by
    ext y
    simp only [Finset.mem_image,low,hi,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨x,h,rfl⟩
      simpa [inv] using h
    · intro h
      exact ⟨f y,by simpa [inv] using h,inv y⟩
  have hc : low.card = hi.card := by
    rw [←image,Finset.card_image_of_injective _ (Function.LeftInverse.injective inv)]
  have complement : lowᶜ=hi := by
    ext v
    have ne := hfne v
    simp [low,hi,not_lt,le_iff_lt_or_eq,ne.symm]
  have := Finset.card_compl low
  rw [complement,Fintype.card_fin] at this
  have := Finset.card_le_univ low
  simp only [Fintype.card_fin] at this
  omega

noncomputable def missingColor (g : Coloring n n) (x : Fin n) := (unique_missing g x).choose

theorem absent_missing (g : Coloring n n) (x) : Absent g x (missingColor g x) :=
  (unique_missing g x).choose_spec.1

theorem missing_injective (hn : n%2=1) (g : Coloring n n) :
    Function.Injective (missingColor g) := by
  apply Finite.injective_iff_surjective.mpr
  intro c
  obtain ⟨v,h⟩ := missing_somewhere hn g c
  exact ⟨v,((unique_missing g v).choose_spec.2 _ h).symm⟩

/-- Extend each color matching over the extra point. Diagonal entries play no role. -/
noncomputable def augment (hn : n%2=1) (g : Coloring n n) : Coloring (n+1) n where
  paint := Fin.lastCases (Fin.lastCases (⟨0,by omega⟩ : Fin n) (missingColor g))
    (fun x => Fin.lastCases (missingColor g x) (g.paint x))
  symm := by
    intro x y
    cases x using Fin.lastCases <;> cases y using Fin.lastCases <;>
      simp [Fin.lastCases_last,Fin.lastCases_castSucc,g.symm]
  proper := by
    intro x y z
    cases x using Fin.lastCases <;> cases y using Fin.lastCases <;> cases z using Fin.lastCases <;>
      simp only [Fin.lastCases_last,Fin.lastCases_castSucc,ne_eq,Fin.castSucc_inj] <;> intro xy xz eq
    all_goals first
      | contradiction
      | trivial
      | exact False.elim (xy rfl)
      | exact False.elim (xz rfl)
      | rfl
      | exact (missing_injective hn g) eq
      | exact g.proper _ _ _ xy xz eq
      | exact False.elim ((absent_missing g _ _ xy) eq)
      | exact False.elim ((absent_missing g _ _ xz) eq.symm)

@[simp] theorem augment_paint (hn : n%2=1) (g : Coloring n n) (x y : Fin n) :
    (augment hn g).paint x.castSucc y.castSucc = g.paint x y := by simp [augment]

/-- One partner of each color at each point of an even complete graph. -/
theorem has_partner (g : Coloring (n+1) n) (v : Fin (n+1)) (c : Fin n) :
    ∃ u, v ≠ u ∧ g.paint v u=c := by
  classical
  let other := ((univ : Finset (Fin (n+1))).erase v)
  have full : other.image (g.paint v)=univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn]
    · simp [other]
    · intro x hx y hy eq
      exact g.proper _ _ _ (Finset.mem_erase.mp hx).1.symm (Finset.mem_erase.mp hy).1.symm eq
  obtain ⟨u,hu,eq⟩ := Finset.mem_image.mp (show c ∈ other.image (g.paint v) by simp [full])
  exact ⟨u,(mem_erase.mp hu).1.symm,eq⟩

noncomputable def mate (g : Coloring (n+1) n) (c : Fin n) (v) := (has_partner g v c).choose

theorem mate_spec (g : Coloring (n+1) n) (c : Fin n) (v) :
    v ≠ mate g c v ∧ g.paint v (mate g c v)=c := (has_partner g v c).choose_spec

theorem mate_involutive (g : Coloring (n+1) n) (c : Fin n) : Function.Involutive (mate g c) := by
  intro v
  obtain ⟨ne,eq⟩ := mate_spec g c v
  obtain ⟨ne',eq'⟩ := mate_spec g c (mate g c v)
  exact g.proper _ _ _ ne' ne.symm (eq'.trans ((g.symm _ _).trans eq).symm)
end WildExact
