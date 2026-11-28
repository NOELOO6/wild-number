import AnchoredGraph

namespace WildAnchor
open WildExact

variable {m n k : Nat}

/-- The anchor and a companion matching alternate in the indicated
cycles, in this companion's own vertex coordinates. -/
def AlternatingChart (g : Coloring n k) (a c : Fin k) (next : Equiv.Perm (Fin m))
    (w : Point m ≃ Fin n) : Prop :=
  (∀ i,g.paint (w (i,false)) (w (i,true))=a) ∧
    ∀ i,g.paint (w (i,false)) (w (next i,true))=c

private def opposite (z : Point m) : Point m := (z.1,!z.2)

private theorem anchor_opposite (g : Coloring n k) (a : Fin k) (e : Point m ≃ Fin n)
    (anchor : ∀ i,g.paint (e (i,false)) (e (i,true))=a) (z : Point m) :
    g.paint (e z) (e (opposite z))=a := by
  obtain ⟨i,b⟩ := z
  cases b
  · exact anchor i
  · exact (g.symm _ _).trans (anchor i)

private theorem opposite_ne (z : Point m) : z≠opposite z := by
  obtain ⟨i,b⟩ := z
  cases b <;> simp [opposite]

/-- Every two enumerations of the same perfect matching differ by a
permutation of its edges and independent flips of their endpoints. -/
theorem align_anchor (g : Coloring n k) (a : Fin k) (e w : Point m ≃ Fin n)
    (ce : ∀ i,g.paint (e (i,false)) (e (i,true))=a)
    (cw : ∀ i,g.paint (w (i,false)) (w (i,true))=a) :
    ∃ q : Shuffle (Fin m),∀ z,e (perm q z)=w z := by
  let h := w.trans e.symm
  have back (z : Point m) : e (h z)=w z := e.apply_symm_apply _
  have paired (i : Fin m) : h (i,true)=opposite (h (i,false)) := by
    apply e.injective
    apply g.proper (e (h (i,false)))
    · exact e.injective.ne (h.injective.ne (by simp))
    · exact e.injective.ne (opposite_ne _)
    · rw [back,back,cw]
      exact (anchor_opposite g a e ce (h (i,false))).symm.trans (by rw [back])
  let k (i : Fin m) := (h (i,false)).1
  have inj : Function.Injective k := by
    intro i j same
    by_cases b : (h (i,false)).2=(h (j,false)).2
    · exact (Prod.mk.inj (h.injective (Prod.ext same b))).1
    · have neg : (h (i,false)).2= !(h (j,false)).2 := by
        cases u : (h (i,false)).2 <;> cases v : (h (j,false)).2 <;> simp_all
      have eq : h (i,false)=h (j,true) := by rw [paired]; exact Prod.ext same neg
      exact False.elim (Bool.false_ne_true (Prod.mk.inj (h.injective eq)).2)
  let σ := Equiv.ofBijective k ⟨inj,Finite.surjective_of_injective inj⟩
  let q : Shuffle (Fin m) := (σ,fun i => (h (i,false)).2)
  refine ⟨q,fun z => ?_⟩
  rw [←back z]
  apply congrArg e
  obtain ⟨i,b⟩ := z
  cases b
  · exact Prod.ext rfl (by simp [perm,q])
  · rw [paired]
    exact Prod.ext rfl (by simp [perm,q,opposite])

/-- Separate alternating cycle witnesses suffice. No synchronization of
the individual witnesses is needed as a graph hypothesis. -/
theorem frame_of_charts (g : Coloring n k) (a : Fin k) (next : {c : Fin k // c≠a} → Equiv.Perm (Fin m))
    (companion : {c : Fin k // c≠a})
    (charts : ∀ c,∃ w,AlternatingChart g a c.val (next c) w) :
    ∃ e,InFrame g a e next := by
  obtain ⟨e,one⟩ := charts companion
  refine ⟨e,one.1,fun c => ?_⟩
  obtain ⟨w,loc⟩ := charts c
  obtain ⟨q,rel⟩ := align_anchor g a e w one.1 loc.1
  exact ⟨q,fun i => by simpa only [rel] using loc.2 i⟩
end WildAnchor
