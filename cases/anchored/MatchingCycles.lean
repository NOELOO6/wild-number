import AlternatingLists

namespace WildAnchor.Alternating
open Function Finset WildExact
variable {n m : Nat}

noncomputable def colorPair (g : Coloring (n+1) n) (a c : Fin n) : Pairing (Fin (n+1)) where
  first := mate g a
  second := mate g c
  first_inv := mate_involutive g a
  second_inv := mate_involutive g c
  first_moves x := (mate_spec g a x).1.symm
  second_moves x := (mate_spec g c x).1.symm

theorem one_step_moves (g : Coloring (n+1) n) (a c : Fin n) (ne : c≠a) (x : Fin (n+1)) :
    (colorPair g a c).step x≠x := by
  intro eq
  change mate g a (mate g c x)=x at eq
  have same : mate g c x=mate g a x :=
    ((mate_involutive g a) _).symm.trans (congrArg (mate g a) eq)
  exact ne ((mate_spec g c x).2.symm.trans (same ▸ (mate_spec g a x).2))

theorem min_two (g : Coloring (n+1) n) (a c : Fin n) (ne : c≠a) (x : Fin (n+1)) :
    2≤(colorPair g a c).period x := by
  let P := colorPair g a c
  have pos := P.period_pos x
  have back : P.point x (P.period x)=x := iterate_minimalPeriod
  by_contra! h
  change P.period x<2 at h
  rw [show P.period x=1 by omega] at back
  exact one_step_moves g a c ne x back

/-- Following a companion edge and an anchor edge twice never returns to
the start. For distinct colors this is precisely the absence of an
alternating four-cycle. -/
def NoFourCycle (g : Coloring (n+1) n) (a c : Fin n) : Prop :=
  ∀ x : Fin (n+1),mate g a (mate g c (mate g a (mate g c x)))≠x

theorem min_three (g : Coloring (n+1) n) (a c : Fin n) (ne : c≠a) (four : NoFourCycle g a c)
    (x : Fin (n+1)) : 3≤(colorPair g a c).period x := by
  let P := colorPair g a c
  have two := min_two g a c ne x
  have back : P.point x (P.period x)=x := iterate_minimalPeriod
  by_contra! bad
  change P.period x<3 at bad
  change 2≤P.period x at two
  rw [show P.period x=2 by omega] at back
  exact four x back

/-- Transfer the sorted cycle enumeration to the permutation convention
used by a finite cut table. -/
theorem charts_of_periods (g : Coloring (n+1) n) (a c : Fin n) (size : n+1=2*m) (lo : Nat)
    (positive : 0<lo) (low : ∀ x,lo≤(colorPair g a c).period x)
    (table : (cycleLists m lo m).all (fun cs => (List.finRange m).all fun i =>
      ((cyclePerm m cs) i).val==successor cs i.val)=true) :
    ∃ cs,OrderedCycles m lo cs ∧ ∃ w,AlternatingChart g a c (cyclePerm m cs) w := by
  obtain ⟨cs,ord,w,first,second⟩ := (colorPair g a c).sorted_cycles
    ((Fintype.card_fin _).trans size) lo low
  have row := List.all_eq_true.mp table cs (cycle_member positive ord)
  exact ⟨cs,ord,w,fun i => (first i) ▸ (mate_spec g a (w (i,false))).2,
    fun i => (second i _ (beq_iff_eq.mp (List.all_eq_true.mp row i (List.mem_finRange i)))) ▸
      (mate_spec g c (w (i,false))).2⟩

end WildAnchor.Alternating
