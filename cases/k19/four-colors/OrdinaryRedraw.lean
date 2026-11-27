import PaletteGraph
namespace WildPalette
open WildExact WildSieve EdgeWalk Finset

/-- The entire hypothesis can be read off the ordinary nineteen-point
coloring: each unchanged color has exactly the edges in the supplied row. -/
def KeepsOrdinary (g : Coloring 19 19) (P : Finset C) :=
  ∀ c,c∉P → ∀ a b : Fin 19,a≠b → (g.paint a b=c ↔ Adj (K19Exchange.color c) a b)

private theorem table_matches : ∀ c : C,∀ a b : Fin 19,
    Adj (K19Exchange.color c) a b ↔ partner c a.castSucc=b.castSucc := by unfold Adj; native_decide
private theorem perfect : ∀ c x, x≠partner c x ∧ partner c (partner c x)=x := by native_decide

theorem completed_fixed (g : Coloring 19 19) (P : Finset C) (keep : KeepsOrdinary g P) :
    Fixed (augment (by decide) g) P := by
  let F := augment (by decide) g
  intro c nc
  have ordinary (a : Fin 19) : mate F c a.castSucc=partner c a.castSucc := by
    apply F.proper _ _ _ (mate_spec F c _).1 (perfect c _).1
    rw [(mate_spec F c _).2]
    by_cases root : partner c a.castSucc=Fin.last 19
    · have absent : Absent g a c := by
        intro b ab col
        have eq := (table_matches c a b).mp ((keep c nc a b ab).mp col)
        exact Fin.castSucc_ne_last b (eq.symm.trans root)
      have miss : missingColor g a=c := ((unique_missing g a).choose_spec.2 c absent).symm
      rw [root]
      simp only [F,augment,Fin.lastCases_castSucc,Fin.lastCases_last,miss]
    · obtain ⟨b,hb⟩ := before_root _ root
      have ne : a≠b := fun e => (perfect c _).1 ((congrArg Fin.castSucc e).trans hb)
      have col := (keep c nc a b ne).mpr ((table_matches c a b).mpr hb.symm)
      rw [←hb,show F.paint a.castSucc b.castSucc=g.paint a b from augment_paint _ _ _ _]
      exact col.symm
  intro x
  cases x using Fin.lastCases with
  | cast a => exact ordinary a
  | last =>
    obtain ⟨b,eq⟩ := before_root (partner c (Fin.last 19)) (perfect c _).1.symm
    have br : mate F c b.castSucc=Fin.last 19 := (ordinary b).trans (eq ▸ (perfect c (Fin.last 19)).2)
    exact (br ▸ mate_involutive F c b.castSucc).trans eq

/-- Any proper redraw of any four colors of the ordinary K19 drawing has
wild number thirteen. A single witness works for all redraws of a given
choice of four colors. -/
theorem four_ordinary (P : Finset C) (four : P.card=4) :
    (∃ w : Lines 19,Legal w ∧ w.card≤13 ∧ ∀ g : Coloring 19 19,KeepsOrdinary g P → Works g w) ∧
    ∀ g : Coloring 19 19,KeepsOrdinary g P → Exact g 13 := by
  obtain ⟨w,legal,sz,all⟩ := common_thirteen P four
  exact ⟨⟨w,legal,sz,fun g h => all g (completed_fixed g P h)⟩,
    fun g h => (exact_four P four).1 g (completed_fixed g P h)⟩

#print axioms four_ordinary
end WildPalette
