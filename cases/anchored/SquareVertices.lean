import MatchingCycles

namespace WildAnchor.Alternating
open WildExact Finset
variable {m n : Nat}

/-- Vertices lying on a four-cycle of the two indicated colors, for
distinct colors in a minimum coloring of an even-order complete graph. -/
noncomputable def squareVertices (g : Coloring (n+1) n) (a c : Fin n) := by
  classical
  exact univ.filter fun x => (colorPair g a c).step ((colorPair g a c).step x)=x

private def advancePair (next : Equiv.Perm (Fin m)) (p : Point m) : Point m :=
  if p.2 then (next.symm p.1,true) else (next p.1,false)

def squareInChart (next : Equiv.Perm (Fin m)) :=
  (univ.filter (fun p : Point m => advancePair next (advancePair next p)=p)).card

theorem square_in_chart (g : Coloring (n+1) n) (a c : Fin n) (next : Equiv.Perm (Fin m))
    (w : Point m ≃ Fin (n+1)) (chart : AlternatingChart g a c next w) :
    (squareVertices g a c).card=squareInChart next := by
  classical
  have partner (col : Fin n) (x y : Fin (n+1)) (ne : x≠y) (edge : g.paint x y=col) :
      mate g col x=y := g.proper _ _ _ (mate_spec g col x).1 ne ((mate_spec g col x).2.trans edge.symm)
  let P := colorPair g a c
  have move (p : Point m) : P.step (w p)=w (advancePair next p) := by
    rcases p with ⟨i,b⟩
    cases b
    · change mate g a (mate g c (w (i,false)))=w (next i,false)
      rw [partner c _ _ (w.injective.ne (by simp)) (chart.2 i)]
      exact partner a _ _ (w.injective.ne (by simp)) ((g.symm _ _).trans (chart.1 _))
    · change mate g a (mate g c (w (i,true)))=w (next.symm i,true)
      have edge : g.paint (w (i,true)) (w (next.symm i,false))=c := by
        simpa only [Equiv.apply_symm_apply] using (g.symm _ _).trans (chart.2 (next.symm i))
      rw [partner c _ _ (w.injective.ne (by simp)) edge]
      exact partner a _ _ (w.injective.ne (by simp)) (chart.1 _)
  have eq : (univ.filter (fun p : Point m => advancePair next (advancePair next p)=p)).map w.toEmbedding =
      squareVertices g a c := by
    ext x
    obtain ⟨p,rfl⟩ := w.surjective x
    simp only [mem_map_equiv,squareVertices,mem_filter,mem_univ,true_and,Equiv.symm_apply_apply]
    change advancePair next (advancePair next p)=p ↔ P.step (P.step (w p))=w p
    rw [move,move,Equiv.apply_eq_iff_eq]
  rw [←eq,card_map]
  rfl

end WildAnchor.Alternating
