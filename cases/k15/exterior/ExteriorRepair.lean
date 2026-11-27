import ExteriorGraph
import ResidualCuts
namespace WildExterior
open Finset WildSieve WildExact

private theorem in_half {A B C : Finset V} (h : C∈({A,B}:Blocks V)) : C⊆A∪B := by
  rcases mem_insert.mp h with rfl|k
  · exact subset_union_left
  · rw [mem_singleton.mp k];exact subset_union_right

private theorem half_size {i : Port ↪ V} {A B C : Finset V} (s : Split i A B)
    (h : C∈({A,B}:Blocks V)) : C.card=3 := by
  rcases mem_insert.mp h with rfl|k
  · exact s.a
  · rw [mem_singleton.mp k];exact s.b

/-- Once the exterior is clear, joining the six fixed vertices in a single
tree works for every color. The complete set of eleven wild edges is the
union of this tree and the three two-edge trees on the exterior. -/
theorem joined_six_works (g : Coloring 15 15) (i : Port ↪ V) (out : root∉outside i)
    (rule : ∀ c,Inside (coloringFactor (augment (by decide) g)) c (outside i)ᶜ≤2)
    (L : Layout (univ : Finset Port))
    (pass : ∀ t∈L.val,Clear (coloringFactor (augment (by decide) g)) i root t) :
    let H := (outside i)ᶜ.erase root
    let w := spokes (oldPart H) ∪ drawing (outsideBlocks i L)
    Legal w ∧ w.card≤11 ∧ Works g w := by
  classical
  let F := coloringFactor (augment (by decide) g)
  let H := (outside i)ᶜ.erase root
  let O := outsideBlocks i L
  let w := spokes (oldPart H) ∪ drawing O
  obtain ⟨A,B,s⟩ := split_exists i out
  have h6 : H.card=6 := by rw [card_erase_of_mem (mem_compl.mpr out),seven]
  have nr : root∉H := not_mem_erase _ _
  have ⟨ot,ov⟩ := outside_blocks i L
  have n := ot.card_vertices
  rw [ov,nine] at n
  have os : O.card=3 := by change (outsideBlocks i L).card=3;omega
  have away : Disjoint H (outside i) := disjoint_compl_left.mono_left (erase_subset _ _)
  have oroot (T : Finset V) (ht : T∈O) : root∉T := fun h => out (ov ▸ block_sub ht h)
  have bound : (drawing O).card≤6 := by
    apply card_biUnion_le.trans
    calc
      _≤∑ _∈O,2 := sum_le_sum (fun T ht => (spokes_bound _).trans (by rw [old_size T (oroot T ht),ot.size T ht]))
      _=6 := by simp [os]
  refine ⟨fun e he => ?_,?_,?_⟩
  · rcases mem_union.mp he with h|h
    · exact spokes_legal _ e h
    · exact draw_legal _ e h
  · have far := spokes_bound (oldPart H)
    rw [old_size H nr,h6] at far
    exact (card_union_le _ _).trans ((Nat.add_le_add far bound).trans (by decide))
  intro c x y
  apply Classical.byContradiction
  intro lost
  obtain ⟨tri,cover⟩ := split_layout s out L
  let D := allBlocks i A B L
  have joined (Q : Finset V) (all : ∀ T : Finset V,root∉T → spokes (oldPart T)⊆w → Cohesive T Q)
      (T : Finset V) (ht : T∈D) : Cohesive T Q := by
    have allH := all H nr subset_union_left
    have sub (C : Finset V) (hc : C⊆H) : Cohesive C Q := fun x hx y hy => allH x (hc hx) y (hc hy)
    rcases all_mem.mp ht with rfl|rfl|⟨t,tl,rfl⟩
    · exact sub _ (by change _⊆(outside i)ᶜ.erase root;rw [←s.inside];exact subset_union_left)
    · exact sub _ (by change _⊆(outside i)ᶜ.erase root;rw [←s.inside];exact subset_union_right)
    · have inO : t.map i∈O := mem_image.mpr ⟨t,tl,rfl⟩
      exact all _ (oroot _ inO) ((draw_mem inO).trans subset_union_right)
  obtain ⟨Q,cl,all,kind⟩ := small_closed_side g w c x y lost D tri cover joined
  obtain ⟨C,hc,side⟩ := residual_cuts F i s rule L pass c Q cl kind
  have sz := half_size s hc
  have ch : C⊆H := by change C⊆(outside i)ᶜ.erase root;rw [←s.inside];exact in_half hc
  have first : C⊆Q := by
    rcases side with eq|⟨t,_,eq⟩
    · rw [eq];exact subset_insert _ _
    · rw [eq];exact subset_union_left
  obtain ⟨z,hz⟩ := card_pos.mp (show 0<C.card by omega)
  have full : H⊆Q := fun v hv => all H nr subset_union_left z (ch hz) v hv (first hz)
  have back : H⊆C := by
    intro v hv
    have vq := full hv
    rcases side with eq|⟨t,ht,eq⟩
    · rw [eq] at vq
      exact (mem_insert.mp vq).resolve_left (fun vr => nr (vr ▸ hv))
    · apply (mem_union.mp (eq ▸ vq)).resolve_right
      rintro mem
      obtain ⟨u,_,eu⟩ := mem_map.mp mem
      exact disjoint_left.mp away hv (outside_mem.mpr ⟨u,eu⟩)
  have := card_le_card back
  omega

/-- An arbitrary choice of the six satisfying the seven-point rule may be
preserved as a single group. The other nine can be partitioned after up to
four named exterior triples have been excluded. -/
theorem k15_keep_six (g : Coloring 15 15) (i : Port ↪ V) (out : root∉outside i)
    (rule : ∀ c,Inside (coloringFactor (augment (by decide) g)) c (outside i)ᶜ≤2)
    (E : Finset (Finset Port)) (few : E.card≤4) :
    ∃ L : Layout (univ : Finset Port), (∀ t∈L.val,t∉E) ∧
      let H := (outside i)ᶜ.erase root
      let w := spokes (oldPart H) ∪ drawing (outsideBlocks i L)
      Legal w ∧ w.card≤11 ∧ Works g w := by
  obtain ⟨L,p⟩ := exterior_graph _ i root out rule E few
  exact ⟨L,fun t ht => (p t ht).2,joined_six_works g i out rule L (fun t ht => (p t ht).1)⟩

/-- A split of the fixed six that clears its own two root cuts and has at
most four additional forbidden exterior triples yields ten wild edges. -/
theorem ten_after_split (g : Coloring 15 15) (i : Port ↪ V) (out : root∉outside i)
    (A B : Finset V) (s : Split i A B)
    (rule : ∀ c,Inside (coloringFactor (augment (by decide) g)) c (outside i)ᶜ≤2)
    (E : Finset (Finset Port)) (few : E.card≤4)
    (base : ∀ c C,C∈({A,B}:Blocks V) → ¬Closed ((coloringFactor (augment (by decide) g)).f c) (insert root C))
    (mixed : ∀ t : Finset Port,t.card=3 → t∉E → Clear (coloringFactor (augment (by decide) g)) i root t →
      ∀ c C,C∈({A,B}:Blocks V) → ¬Closed ((coloringFactor (augment (by decide) g)).f c) (C∪t.map i)) :
    Exact g 10 := by
  let F := coloringFactor (augment (by decide) g)
  obtain ⟨L,hL⟩ := exterior_graph F i root out rule E few
  let D := allBlocks i A B L
  obtain ⟨tri,cover⟩ := split_layout s out L
  have ex (c Q) (cl : Closed (F.f c) Q) (kind : (∃ T∈D,Q=insert root T) ∨
      (∃ T∈D,∃ U∈D,T≠U ∧ Q=T∪U)) : False := by
    obtain ⟨C,hc,rs⟩ := residual_cuts F i s rule L (fun t ht => (hL t ht).1) c Q cl kind
    rcases rs with rfl|⟨t,ht,rfl⟩
    · exact base c C hc cl
    · exact mixed t (L.property.1.size t ht) (hL t ht).2 (hL t ht).1 c C hc cl
  have upper := ten_from_five g D tri cover (fun c T ht cl => ex c _ cl (Or.inl ⟨T,ht,rfl⟩))
    (fun c T ht U hu ne cl => ex c _ cl (Or.inr ⟨T,ht,U,hu,ne,rfl⟩))
  obtain ⟨w,leg,sz,work⟩ := upper
  have lb : ∀ v,Legal v → Works g v → 10≤v.card := fun _ h p => odd_lower (by decide) g h p
  exact ⟨⟨w,leg,Nat.le_antisymm sz (lb w leg work),work⟩,lb⟩

#print axioms k15_keep_six
#print axioms joined_six_works
#print axioms ten_after_split
end WildExterior
