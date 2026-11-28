import MatchingModel
import UniversalLower
import StarDraw
import LegalEdges

namespace WildExact.RootContraction
open Finset WildDeletion
variable {n : Nat}

private def project (a : Fin n) : Fin (n+1) → Fin n := Fin.lastCases a id
@[simp] private theorem old (a x : Fin n) : project a x.castSucc=x := by simp [project]
@[simp] private theorem root (a : Fin n) : project a (Fin.last n)=a := by simp [project]

/-- Project the wild edges to the ordinary vertices, remove loops and identify duplicates. -/
def shrink (a : Fin n) (w : Lines (n+1)) : Lines n :=
  (w.filter (fun e => project a e.1≠project a e.2)).image
    (fun e => WildCuts.ordered (project a e.1,project a e.2))

private theorem ordered_legal {x y : Fin n} (ne : x≠y) :
    (WildCuts.ordered (x,y)).1 < (WildCuts.ordered (x,y)).2 := by
  by_cases h : x≤y
  · simpa [WildCuts.ordered,h] using lt_of_le_of_ne h ne
  · simpa [WildCuts.ordered,h] using lt_of_not_ge h

theorem legal (a : Fin n) (w : Lines (n+1)) : Legal (shrink a w) := by
  intro e he
  obtain ⟨f,hf,rfl⟩ := mem_image.mp he
  exact ordered_legal (mem_filter.mp hf).2

theorem size (a : Fin n) (w : Lines (n+1)) : (shrink a w).card≤w.card :=
  card_image_le.trans (card_le_card (filter_subset _ _))

theorem saves_edge {a : Fin n} {w : Lines (n+1)} (incident : Touch w a.castSucc (Fin.last n)) :
    (shrink a w).card<w.card := by
  let kept := w.filter (fun e => project a e.1≠project a e.2)
  have ss : kept ⊂ w := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨filter_subset _ _,fun same => ?_⟩
    rcases incident with h|h
    · have := (mem_filter.mp (same ▸ h : (a.castSucc,Fin.last n)∈kept)).2
      simp at this
    · have := (mem_filter.mp (same ▸ h : (Fin.last n,a.castSucc)∈kept)).2
      simp at this
  exact card_image_le.trans_lt (card_lt_card ss)

private theorem touch_ordered {w : Lines n} {x y : Fin n} (mem : WildCuts.ordered (x,y)∈w) :
    Touch w x y := by
  by_cases h : x≤y
  · exact Or.inl (by simpa [WildCuts.ordered,h] using mem)
  · exact Or.inr (by simpa [WildCuts.ordered,h] using mem)

private theorem project_touch {a : Fin n} {w : Lines (n+1)} {x y : Fin (n+1)}
    (ne : project a x≠project a y) (h : Touch w x y) :
    Touch (shrink a w) (project a x) (project a y) := by
  rcases h with h|h
  · exact touch_ordered (mem_image.mpr ⟨(x,y),mem_filter.mpr ⟨h,ne⟩,rfl⟩)
  · exact Or.symm (touch_ordered (mem_image.mpr ⟨(y,x),mem_filter.mpr ⟨h,ne.symm⟩,rfl⟩))

noncomputable def partner (g : Coloring (n+1) n) (c : Fin n) : Fin n :=
  (WildSieve.before_root _ (mate_spec g c (Fin.last n)).1.symm).choose

theorem partner_paint (g : Coloring (n+1) n) (c : Fin n) :
    g.paint (Fin.last n) (partner g c).castSucc=c := by
  rw [show (partner g c).castSucc=mate g c (Fin.last n) from
    (WildSieve.before_root _ (mate_spec g c (Fin.last n)).1.symm).choose_spec]
  exact (mate_spec g c _).2

theorem partner_unique (g : Coloring (n+1) n) (c x : Fin n)
    (h : g.paint (Fin.last n) x.castSucc=c) : x=partner g c :=
  Fin.castSucc_inj.mp (g.proper _ _ _ (Fin.castSucc_ne_last x).symm
    (Fin.castSucc_ne_last _).symm (h.trans (partner_paint g c).symm))

/-- In each color, adding the edge to its former root partner reconnects the projection. -/
theorem two_components (g : Coloring (n+1) n) {w : Lines (n+1)} (win : Works g w)
    (a c x : Fin n) :
    Walk (Joined (restrict g) (shrink a w) c) a x ∨
      Walk (Joined (restrict g) (shrink a w) c) (partner g c) x := by
  let E := Joined (restrict g) (shrink a w) c
  let P := fun v : Fin (n+1) => Walk E a (project a v) ∨ Walk E (partner g c) (project a v)
  have step (u v : Fin (n+1)) (h : Joined g w c u v) (hu : P u) : P v := by
    by_cases eq : project a u=project a v
    · simpa only [P,←eq] using hu
    have follow (edge : E (project a u) (project a v)) : P v :=
      hu.elim (fun p => Or.inl (.step p edge)) (fun p => Or.inr (.step p edge))
    rcases h with wild|⟨ne,col⟩
    · exact follow (Or.inl (project_touch eq wild))
    · cases v using Fin.lastCases with
      | last => exact Or.inl (by simpa using (Walk.stay (E:=E) a))
      | cast y =>
        cases u using Fin.lastCases with
        | last =>
          have h := partner_unique g c y col
          exact Or.inr (by simpa [h] using (Walk.stay (E:=E) (partner g c)))
        | cast z =>
          apply follow (Or.inr ?_)
          simpa [E,restrict] using And.intro (fun same : z=y => ne (congrArg Fin.castSucc same)) col
  have all {u v} (p : Walk (Joined g w c) u v) : P u → P v := by
    induction p with
    | stay => exact id
    | step _ e ih => exact fun h => step _ _ e (ih h)
  have init : P a.castSucc := Or.inl (by simpa using (Walk.stay (E:=E) a))
  simpa [P,E] using all (win c a.castSucc x.castSucc) init

/-- Add one ordinary edge, omitting a loop if the endpoints coincide. -/
def repair (w : Lines n) (a z : Fin n) : Lines n :=
  if a=z then w else insert (WildCuts.ordered (a,z)) w

private theorem repair_sub (w : Lines n) (a z : Fin n) : w⊆repair w a z := by
  by_cases eq : a=z <;> simp [repair,eq]

theorem repair_legal {w : Lines n} (leg : Legal w) (a z : Fin n) : Legal (repair w a z) := by
  by_cases eq : a=z
  · simpa [repair,eq] using leg
  · intro e he
    rcases mem_insert.mp (show e∈insert (WildCuts.ordered (a,z)) w by simpa [repair,eq] using he) with h|h
    · exact h ▸ ordered_legal eq
    · exact leg e h

theorem repair_size (w : Lines n) (a z : Fin n) : (repair w a z).card≤w.card+1 := by
  by_cases eq : a=z
  · simp [repair,eq]
  · simpa [repair,eq] using card_insert_le (WildCuts.ordered (a,z)) w

theorem lift_walk {g : Coloring n n} {w : Lines n} {a z c u v : Fin n}
    (p : Walk (Joined g w c) u v) : Walk (Joined g (repair w a z) c) u v := by
  apply Walk.mapInto id _ p
  intro x y h
  exact .step (.stay _) (h.elim (fun t => Or.inl (t.imp
    (fun h => repair_sub w a z h) (fun h => repair_sub w a z h))) Or.inr)

theorem link (g : Coloring n n) (w : Lines n) (c a z : Fin n) :
    Walk (Joined g (repair w a z) c) a z := by
  by_cases eq : a=z
  · exact eq ▸ Walk.stay _
  · exact .step (.stay _) (Or.inl (touch_ordered (by simp [repair,eq])))

private theorem works_of_bridges (g : Coloring (n+1) n) {w : Lines (n+1)} (win : Works g w)
    (a u v : Fin n) (bridges : ∀ c,
      Walk (Joined (restrict g) (repair (shrink a w) u v) c) a (partner g c)) :
    Works (restrict g) (repair (shrink a w) u v) := by
  intro c
  let E := Joined (restrict g) (repair (shrink a w) u v) c
  have all (x : Fin n) : Walk E a x :=
    (two_components g win a c x).elim lift_walk (fun h => (bridges c).join (lift_walk h))
  exact fun x y => (backwards (joined_symm (restrict g)) (all x)).join (all y)

/-- One endpoint is shared across all colors. Each split color needs the other endpoint
in the component of its former root partner. -/
theorem repair_works (g : Coloring (n+1) n) {w : Lines (n+1)} (win : Works g w)
    (a z : Fin n) (hit : ∀ c, Walk (Joined (restrict g) (shrink a w) c) a (partner g c) ∨
      Walk (Joined (restrict g) (shrink a w) c) z (partner g c)) :
    Works (restrict g) (repair (shrink a w) a z) := by
  apply works_of_bridges g win
  intro c
  exact (hit c).elim lift_walk (fun h => (link _ _ c a z).join (lift_walk h))

theorem reverse_upper (g : Coloring (n+1) n) {w : Lines (n+1)} (win : Works g w)
    {a z : Fin n} (incident : Touch w a.castSucc (Fin.last n))
    (hit : ∀ c, Walk (Joined (restrict g) (shrink a w) c) a (partner g c) ∨
      Walk (Joined (restrict g) (shrink a w) c) z (partner g c)) : Upper (restrict g) w.card :=
  ⟨_,repair_legal (legal a w) a z,(repair_size _ a z).trans (saves_edge incident),repair_works g win a z hit⟩

/-- Ordinary vertices on the side opposite a after a root contraction. -/
noncomputable def far (g : Coloring (n+1) n) (w : Lines (n+1)) (a c : Fin n) : Finset (Fin n) := by
  classical
  exact univ.filter fun x => ¬Walk (Joined (restrict g) (shrink a w) c) a x

theorem mem_far {g : Coloring (n+1) n} {w : Lines (n+1)} {a c x : Fin n} :
    x∈far g w a c ↔ ¬Walk (Joined (restrict g) (shrink a w) c) a x := by
  classical
  simp [far]

/-- Distinct colors can have exactly the same cut. Count each nonempty far side once. -/
noncomputable def sides (g : Coloring (n+1) n) (w : Lines (n+1)) (a : Fin n) :=
  ((univ : Finset (Fin n)).image (far g w a)).erase ∅

theorem crossing_works (g : Coloring (n+1) n) {w : Lines (n+1)} (win : Works g w) (a u v : Fin n)
    (hit : ∀ S∈sides g w a,WildCuts.Cross S u v) : Works (restrict g) (repair (shrink a w) u v) := by
  classical
  apply works_of_bridges g win
  intro c
  by_cases done : Walk (Joined (restrict g) (shrink a w) c) a (partner g c)
  · exact lift_walk done
  · have mem : partner g c∈far g w a c := mem_far.mpr done
    have here : far g w a c∈sides g w a :=
      mem_erase.mpr ⟨nonempty_iff_ne_empty.mp ⟨_,mem⟩,mem_image_of_mem _ (mem_univ c)⟩
    let E := Joined (restrict g) (repair (shrink a w) u v) c
    have bridge {x y} (hx : x∉far g w a c) (hy : y∈far g w a c) (edge : Walk E x y) :
        Walk E a (partner g c) := by
      have left := not_not.mp (fun no => hx (mem_far.mpr no))
      have right := (two_components g win a c y).resolve_left (mem_far.mp hy)
      exact ((lift_walk left).join edge).join (lift_walk (backwards (joined_symm _) right))
    have e := link (restrict g) (shrink a w) c u v
    rcases hit _ here with ⟨hu,hv⟩|⟨hv,hu⟩
    · exact bridge hv hu (backwards (joined_symm _) e)
    · exact bridge hu hv e

theorem repair_touch {w : Lines n} {u v x y : Fin n} (h : Touch (repair w u v) x y) :
    Touch w x y ∨ (x=u ∧ y=v) ∨ (x=v ∧ y=u) := by
  by_cases eq : u=v
  · exact Or.inl (by simpa [repair,eq] using h)
  · by_cases le : u≤v
    all_goals
      simp only [repair,eq,if_false,WildCuts.ordered,le,Touch] at h
      rcases h with h|h <;> rcases mem_insert.mp h with h|h
      all_goals first | exact Or.inl (Or.inl h) | exact Or.inl (Or.inr h) |
        cases h; simp

/-- A successful one-edge repair must cross every nonempty far side. -/
theorem crossing_needed (g : Coloring (n+1) n) {w : Lines (n+1)} (a u v : Fin n)
    (win : Works (restrict g) (repair (shrink a w) u v)) :
    ∀ S∈sides g w a,WildCuts.Cross S u v := by
  classical
  intro S hs
  obtain ⟨ne,hi⟩ := mem_erase.mp hs
  obtain ⟨c,_,rfl⟩ := mem_image.mp hi
  obtain ⟨z,hz⟩ := nonempty_iff_ne_empty.mpr ne
  by_contra no
  let S := far g w a c
  have same : u∈S ↔ v∈S := by
    by_cases hu : u∈S <;> by_cases hv : v∈S <;> simp_all [WildCuts.Cross,S]
  have oldStep {x y} (e : Joined (restrict g) (shrink a w) c x y) : x∈S ↔ y∈S := by
    rw [mem_far,mem_far]
    exact not_congr ⟨fun h => .step h e,fun h => .step h (joined_symm _ e)⟩
  have step {x y} (e : Joined (restrict g) (repair (shrink a w) u v) c x y) : x∈S ↔ y∈S := by
    rcases e with wild|col
    · rcases repair_touch wild with old|⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact oldStep (Or.inl old)
      · exact same
      · exact same.symm
    · exact oldStep (Or.inr col)
  have path {x y} (p : Walk (Joined (restrict g) (repair (shrink a w) u v) c) x y) : x∈S ↔ y∈S := by
    induction p with
    | stay => rfl
    | step _ e ih => exact ih.trans (step e)
  exact mem_far.mp ((path (win c a z)).mpr hz) (.stay _)

theorem repair_iff (g : Coloring (n+1) n) {w : Lines (n+1)} (win : Works g w) (a u v : Fin n) :
    Works (restrict g) (repair (shrink a w) u v) ↔ ∀ S∈sides g w a,WildCuts.Cross S u v :=
  ⟨crossing_needed g a u v,crossing_works g win a u v⟩

/-- Any two distinct cut sides can be crossed by a common edge. -/
theorem two_sides_upper (g : Coloring (n+1) n) {w : Lines (n+1)} (win : Works g w)
    {a : Fin n} (incident : Touch w a.castSucc (Fin.last n)) (hn : 2≤n)
    (few : (sides g w a).card≤2) : Upper (restrict g) w.card := by
  classical
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨u,v,_,hit⟩ := WildCuts.cross_all a (sides g w a) id (by omega) (by
    intro S hs
    obtain ⟨hne,h⟩ := mem_erase.mp hs
    obtain ⟨c,_,rfl⟩ := mem_image.mp h
    exact ⟨nonempty_iff_ne_empty.mpr hne,fun ha => mem_far.mp ha (.stay _)⟩)
  exact ⟨_,repair_legal (legal a w) u v,(repair_size _ u v).trans (saves_edge incident),crossing_works g win a u v hit⟩

private theorem shrink_independent {w : Lines (n+1)} (untouched : ∀ x : Fin n,¬Touch w x.castSucc (Fin.last n))
    (a b : Fin n) : shrink a w=shrink b w := by
  have all (a b : Fin n) (e : Fin (n+1) × Fin (n+1)) (he : e∈w) (ne : project a e.1≠project a e.2) :
      WildCuts.ordered (project a e.1,project a e.2)∈shrink b w := by
    obtain ⟨x,y⟩ := e
    cases x using Fin.lastCases <;> cases y using Fin.lastCases
    case last.last => exact (ne rfl).elim
    case last.cast v => exact (untouched v (Or.inr he)).elim
    case cast.last v => exact (untouched v (Or.inl he)).elim
    case cast.cast x y =>
      apply mem_image.mpr
      exact ⟨(x.castSucc,y.castSucc),mem_filter.mpr ⟨he,by simpa using ne⟩,by simp⟩
  have sub (a b : Fin n) (map : ∀ e∈w,project a e.1≠project a e.2 →
      WildCuts.ordered (project a e.1,project a e.2)∈shrink b w) : shrink a w⊆shrink b w := by
    intro f hf
    obtain ⟨e,he,rfl⟩ := mem_image.mp hf
    exact map _ (mem_filter.mp he).1 (mem_filter.mp he).2
  exact Finset.Subset.antisymm (sub a b (all a b)) (sub b a (all b a))

theorem untouched_upper (g : Coloring (n+1) n) {w : Lines (n+1)} (win : Works g w) (a : Fin n)
    (untouched : ∀ x : Fin n,¬Touch w x.castSucc (Fin.last n)) : Upper (restrict g) w.card := by
  refine ⟨shrink a w,legal _ _,size _ _,?_⟩
  intro c x y
  have all (v : Fin n) : Walk (Joined (restrict g) (shrink a w) c) (partner g c) v := by
    rw [shrink_independent untouched a (partner g c)]
    exact (two_components g win (partner g c) c v).elim id id
  exact (backwards (joined_symm _) (all x)).join (all y)

#print axioms untouched_upper
#print axioms two_sides_upper
#print axioms reverse_upper
end WildExact.RootContraction
