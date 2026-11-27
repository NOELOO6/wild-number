import TrimmedEvents
namespace WildSieve
open Finset
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Subdivisions of a region that contain a prescribed smaller subdivision. -/
noncomputable def extensions (X : Finset V) (M : Blocks V) : Finset (Layout X) := by
  classical exact univ.filter (fun D => M⊆D.val)

theorem extension_card (X : Finset V) (M : Blocks V) (valid : Triples M)
    (sub : vertices M⊆X) (k : Nat) (sz : X.card-(vertices M).card=3*k) :
    (extensions X M).card=ways k := by
  classical
  rw [extensions,← Fintype.card_subtype, Fintype.card_congr (completeEquiv X M valid sub)]
  exact card_layout k _ (by rw [card_sdiff sub,sz])

private theorem impossible_extension (J : Finset Nat) (bad : Nat → Finset (Finset V))
    (X : Finset V) {j Y} (hj : j∈J) (hy : Y∈bad j) (M : Layout Y) :
    extensions X M.val ⊆ (admissible J bad X)ᶜ := by
  classical
  intro D h
  exact mem_compl.mpr fun hD => (mem_filter.mp hD).2 j hj Y hy M (mem_filter.mp h).2

/-- A fixed six-point short cut in a twelve-point region excludes all one
hundred combinations of a subdivision on each side. -/
theorem trim_twelve (J : Finset Nat) (bad : Nat → Finset (Finset V))
    (X Y : Finset V) (xs : X.card=12) (ys : Y.card=6) (sub : Y⊆X)
    (hj : 2∈J) (badY : Y∈bad 2) : (admissible J bad X).card≤15300 := by
  classical
  let extn (M : Layout Y) := extensions X M.val
  have dis : ((univ : Finset (Layout Y)) : Set (Layout Y)).PairwiseDisjoint extn := by
    intro M _ N _ ne
    apply disjoint_left.mpr
    intro D hm hn
    have m := (mem_filter.mp hm).2
    have n := (mem_filter.mp hn).2
    have incl (P Q : Layout Y) (p : P.val⊆D.val) (q : Q.val⊆D.val) : P.val⊆Q.val := by
      intro b hb
      obtain ⟨v,hv⟩ := card_pos.mp (show 0<b.card by rw [P.property.1.size b hb]; decide)
      have atQ : v∈vertices Q.val := Q.property.2.symm ▸ P.property.2 ▸ block_sub hb hv
      obtain ⟨a,ha,va⟩ := mem_biUnion.mp atQ
      exact (D.property.1.only (p hb) (q ha) hv va).symm ▸ ha
    exact ne (Subtype.ext (Subset.antisymm (incl M N m n) (incl N M n m)))
  have pieces (M : Layout Y) : (extn M).card=10 :=
    extension_card X M.val M.property.1 (M.property.2.symm ▸ sub) 2 (by rw [M.property.2,xs,ys])
  have sub' : univ.biUnion extn ⊆ (admissible J bad X)ᶜ := by
    intro D h
    obtain ⟨M,_,hm⟩ := mem_biUnion.mp h
    exact impossible_extension J bad X hj badY M hm
  have bound := card_le_card sub'
  rw [card_biUnion dis,card_compl] at bound
  simp only [pieces,sum_const,card_univ,card_layout 2 Y (by omega),nsmul_eq_mul] at bound
  rw [card_layout 4 X (by omega)] at bound
  change 10*10≤15400-(admissible J bad X).card at bound
  omega

/-- Four short triples sharing a point exclude forty different subdivisions
of a nine-point region. -/
theorem trim_nine (J : Finset Nat) (bad : Nat → Finset (Finset V))
    (X : Finset V) (z : V) (family : Finset (Finset V)) (xs : X.card=9)
    (four : family.card=4) (hj : 1∈J)
    (mem : ∀ Q∈family, Q.card=3 ∧ Q⊆X ∧ z∈Q ∧ Q∈bad 1) : (admissible J bad X).card≤240 := by
  classical
  let extn (Q : Finset V) := extensions X {Q}
  have dis : (family : Set (Finset V)).PairwiseDisjoint extn := by
    intro P hp Q hq ne
    apply disjoint_left.mpr
    intro D dp dq
    exact ne (D.property.1.only ((mem_filter.mp dp).2 (mem_singleton_self P))
      ((mem_filter.mp dq).2 (mem_singleton_self Q)) (mem P hp).2.2.1 (mem Q hq).2.2.1)
  have pieces (Q) (hq : Q∈family) : (extn Q).card=10 := by
    obtain ⟨sz,sub,_,_⟩ := mem Q hq
    exact extension_card X {Q} (singleton_triple sz) (by simpa using sub) 2 (by simp [xs,sz])
  have sub' : family.biUnion extn ⊆ (admissible J bad X)ᶜ := by
    intro D h
    obtain ⟨Q,hq,hm⟩ := mem_biUnion.mp h
    obtain ⟨sz,_,_,hy⟩ := mem Q hq
    exact impossible_extension J bad X hj hy ⟨{Q},singleton_triple sz,vertices_singleton Q⟩ hm
  have bound := card_le_card sub'
  rw [card_biUnion dis,card_compl,card_layout 3 X (by omega),
    sum_congr rfl pieces,sum_const,four] at bound
  change 40≤280-(admissible J bad X).card at bound
  omega
end WildSieve
