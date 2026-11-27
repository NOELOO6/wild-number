import RectangleRule

namespace WildRectangle
open Finset WildExact
abbrev V16 := Fin 16
abbrev C15 := Fin 15

private def label (g : Coloring 16 15) (a x : V16) : Option C15 := if a=x then none else some (g.paint a x)

private theorem label_inj (g : Coloring 16 15) (a : V16) : Function.Injective (label g a) := by
  intro x y eq
  by_cases ax : a=x <;> by_cases ay : a=y
  · exact ax.symm.trans ay
  · simp only [label,if_pos ax,if_neg ay,reduceCtorEq] at eq
  · simp only [label,if_neg ax,if_pos ay,reduceCtorEq] at eq
  · exact g.proper a x y ax ay (by simpa [label,ax,ay] using eq)

private theorem label_sym (g : Coloring 16 15) (x y : V16) : label g x y=label g y x := by
  by_cases eq : x=y <;> simp [label,eq,Ne.symm,g.symm]

private noncomputable def colorRows (g : Coloring 16 15) : Rows V16 (Option C15) where
  row a := Equiv.ofBijective (label g a) ((Fintype.bijective_iff_injective_and_card _).mpr ⟨label_inj g a,by simp⟩)
  column := fun x a b eq => label_inj g x ((label_sym g x a).trans (eq.trans (label_sym g b x)))

/-- Fix a deleted point and any two other points. The first triple can
contain both prescribed points, the four points with the root are rainbow,
and the nine edges between the two ordinary triples have distinct colors. -/
theorem prescribed_rectangle (g : Coloring 16 15) (r a b : V16) (ra : r≠a) (rb : r≠b) (ab : a≠b) :
    ∃ (d : V16) (B : Finset V16), d∉({r,a,b}:Finset V16) ∧
      g.paint r d≠g.paint a b ∧ g.paint b d≠g.paint r a ∧ g.paint a d≠g.paint r b ∧
      B⊆({r,a,b,d}:Finset V16)ᶜ ∧ B.card=3 ∧
      ∀ u∈({a,b,d}:Finset V16),∀ v∈B,∀ u'∈({a,b,d}:Finset V16),∀ v'∈B,
        g.paint u v=g.paint u' v' → u=u' ∧ v=v' := by
  classical
  let L := colorRows g
  obtain ⟨d,ne,clean,B,sub,sz,apart⟩ := latin_rectangle L none (fun v => by simp [L,colorRows,label])
    (label_sym g) (by simp) r a b ra rb ab
  obtain ⟨dr,da,db⟩ : d≠r ∧ d≠a ∧ d≠b := by simpa only [mem_insert,mem_singleton,not_or] using ne
  have col (v w : V16) (h : v≠w) : L.row v w=some (g.paint v w) := by simp [L,colorRows,label,h]
  obtain ⟨c1,c2,c3⟩ := clean
  rw [col _ _ dr.symm,col _ _ ab] at c1
  rw [col _ _ db.symm,col _ _ ra] at c2
  rw [col _ _ da.symm,col _ _ rb] at c3
  refine ⟨d,B,ne,(fun h => c1 (congrArg some h)),(fun h => c2 (congrArg some h)),(fun h => c3 (congrArg some h)),sub,sz,?_⟩
  have sep (u v : V16) (ua : u∈({a,b,d}:Finset V16)) (vb : v∈B) : u≠v := by
    rintro rfl
    exact mem_compl.mp (sub vb) (mem_insert_of_mem ua)
  intro u hu v hv w hw z hz eq
  have uv := sep u v hu hv
  have wz := sep w z hw hz
  have same : L.row u v=L.row w z := by rw [col _ _ uv,col _ _ wz,eq]
  have vz : v=z := by
    by_contra diff
    exact disjoint_left.mp (apart hv hz diff) (mem_image.mpr ⟨u,hu,rfl⟩ : L.row u v∈palette L {a,b,d} v)
      (mem_image.mpr ⟨w,hw,same.symm⟩)
  subst z
  exact ⟨L.column v same,rfl⟩

/-- The chosen points of the rectangle are all ordinary vertices after
the standard completion of an arbitrary minimum proper K15 coloring. -/
theorem k15_rectangle (g : Coloring 15 15) (a b : Fin 15) (ab : a≠b) :
    ∃ (d : V16) (B : Finset V16), d∉({Fin.last 15,a.castSucc,b.castSucc}:Finset V16) ∧
      let h := augment (by decide) g
      h.paint (Fin.last 15) d≠h.paint a.castSucc b.castSucc ∧
      h.paint b.castSucc d≠h.paint (Fin.last 15) a.castSucc ∧
      h.paint a.castSucc d≠h.paint (Fin.last 15) b.castSucc ∧
      B⊆({Fin.last 15,a.castSucc,b.castSucc,d}:Finset V16)ᶜ ∧ B.card=3 ∧
      ∀ u∈({a.castSucc,b.castSucc,d}:Finset V16),∀ v∈B,∀ u'∈({a.castSucc,b.castSucc,d}:Finset V16),∀ v'∈B,
        h.paint u v=h.paint u' v' → u=u' ∧ v=v' :=
  prescribed_rectangle _ _ _ _ (Fin.castSucc_ne_last a).symm (Fin.castSucc_ne_last b).symm
    (fun eq => ab (Fin.castSucc_inj.mp eq))

#print axioms k15_rectangle
end WildRectangle
