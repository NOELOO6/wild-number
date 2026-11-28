import SymmetricRepair

namespace WildExact.TripleRepair
open Finset

/-- The color missing at one vertex pairs the other two. -/
def Blocked {n : Nat} (g : Coloring n n) (x y z : Fin n) :=
  x≠y ∧ x≠z ∧ y≠z ∧ (g.paint x y=missingColor g z ∨
    g.paint x z=missingColor g y ∨ g.paint y z=missingColor g x)

noncomputable instance {n : Nat} (g : Coloring n n) (x y z : Fin n) :
    Decidable (Blocked g x y z) := Classical.propDecidable _

/-- A pair has at most three forbidden completions, one for each position
of the vertex missing the obstructing color. -/
theorem blocked_degree {n : Nat} (g : Coloring n n) (odd : n%2=1) (x y : Fin n) :
    (univ.filter (Blocked g x y)).card≤3 := by
  classical
  let A := univ.filter (fun z => missingColor g z=g.paint x y)
  let B := univ.filter (fun z => x≠z ∧ g.paint x z=missingColor g y)
  let C := univ.filter (fun z => y≠z ∧ g.paint y z=missingColor g x)
  have a : A.card≤1 := card_le_one.mpr (fun _ hu _ hv =>
    missing_injective odd g ((mem_filter.mp hu).2.trans (mem_filter.mp hv).2.symm))
  have pair (v : Fin n) (c : Fin n) :
      (univ.filter (fun z => v≠z ∧ g.paint v z=c)).card≤1 := by
    apply card_le_one.mpr
    intro i hi j hj
    obtain ⟨vi,ci⟩ := (mem_filter.mp hi).2
    obtain ⟨vj,cj⟩ := (mem_filter.mp hj).2
    exact g.proper _ _ _ vi vj (ci.trans cj.symm)
  have sub : univ.filter (Blocked g x y) ⊆ (A∪B)∪C := by
    intro z hz
    obtain ⟨_,xz,yz,first|second|third⟩ := (mem_filter.mp hz).2
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨mem_univ _,first.symm⟩))
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨mem_univ _,xz,second⟩))
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,yz,third⟩)
  have b : B.card≤1 := pair _ _
  have c : C.card≤1 := pair _ _
  have u := card_union_le A B
  have w := card_union_le (A∪B) C
  have s := card_le_card sub
  omega

/-- For a color-trapped triple the missing vertex and its opposite edge
give exactly the local obstruction used above. -/
private theorem crossing {n : Nat} (g : Coloring n n) (odd : n%2=1) {x y z : Fin n}
    (xy : x≠y) (xz : x≠z) (yz : y≠z) (ok : ¬Blocked g x y z) (c : Fin n) :
    ∃ u∈({x,y,z} : Finset (Fin n)), ∃ v∉({x,y,z} : Finset (Fin n)), g.paint u v=c := by
  classical
  by_contra! trapped
  let S : Finset (Fin n) := {x,y,z}
  have inside (u v : Fin n) (hu : u∈S) (edge : g.paint u v=c) : v∈S := by
    by_contra outside
    exact trapped u hu v outside edge
  have atZ (a b w : Fin n) (sw : S={a,b,w}) (ab : a≠b) (aw : a≠w) (bw : b≠w)
      (both : g.paint a b=c) : missingColor g w=c := by
    symm
    apply (unique_missing g w).choose_spec.2
    intro v wv edge
    have mem := inside w v (by simp [sw]) edge
    simp only [sw,mem_insert,mem_singleton] at mem
    rcases mem with rfl|rfl|rfl
    · exact bw (g.proper _ _ _ ab aw (both.trans ((g.symm _ _).trans edge).symm))
    · exact aw (g.proper _ _ _ ab.symm bw (((g.symm _ _).trans both).trans ((g.symm _ _).trans edge).symm))
    · exact wv rfl
  by_cases edge : g.paint x y=c
  · exact ok ⟨xy,xz,yz,Or.inl (edge.trans (atZ x y z rfl xy xz yz edge).symm)⟩
  by_cases other : g.paint x z=c
  · have perm : S={x,z,y} := by ext; simp [S,or_comm,or_left_comm]
    exact ok ⟨xy,xz,yz,Or.inr (Or.inl (other.trans (atZ x z y perm xz xy yz.symm other).symm))⟩
  by_cases last : g.paint y z=c
  · have perm : S={y,z,x} := by ext; simp [S,or_comm,or_left_comm]
    exact ok ⟨xy,xz,yz,Or.inr (Or.inr (last.trans (atZ y z x perm yz xy.symm xz.symm last).symm))⟩
  have alone (a b w : Fin n) (sa : S={a,b,w}) (one : g.paint a b≠c) (two : g.paint a w≠c) :
      c=missingColor g a := by
    apply (unique_missing g a).choose_spec.2
    intro v av col
    have mem := inside a v (by simp [sa]) col
    simp only [sa,mem_insert,mem_singleton] at mem
    rcases mem with rfl|rfl|rfl
    · exact av rfl
    · exact one col
    · exact two col
  exact xy (missing_injective odd g ((alone x y z rfl edge other).symm.trans
    (alone y x z (by ext; simp [S,or_left_comm]) (by rwa [g.symm]) last)))

/-- A triple is sealed if one color has no edge leaving it. -/
def SealedTriple {n : Nat} (g : Coloring n n) (S : Finset (Fin n)) : Prop :=
  S.card=3 ∧ ∃ c, ∀ x∈S, ∀ y∉S, g.paint x y≠c

private theorem sealed_degree {n : Nat} (g : Coloring n n) (odd : n%2=1) (x y : Fin n)
    (xy : x≠y) : by classical exact (univ.filter fun z => SealedTriple g {x,y,z}).card≤3 := by
  classical
  apply le_trans _ (blocked_degree g odd x y)
  apply card_le_card
  intro z hz
  obtain ⟨sz,c,trapped⟩ := (mem_filter.mp hz).2
  have xz : x≠z := by
    rintro rfl
    have eq : ({x,y,x} : Finset _)={x,y} := by ext; simp [or_comm,or_left_comm]
    simp [eq,xy] at sz
  have yz : y≠z := by
    rintro rfl
    simp [xy] at sz
  apply mem_filter.mpr ⟨mem_univ _,?_⟩
  by_contra good
  obtain ⟨u,hu,v,hv,edge⟩ := crossing g odd xy xz yz good c
  exact trapped u hu v hv edge

/-- At every odd order 3m with m ≥ 4, an arbitrary minimum coloring has
a partition into triples each of which has an outgoing edge in every color.
The first odd order covered is K15, with five triples. -/
theorem valid_triple_partition (m : Nat) (large : 4≤m) (odd : (m*3)%2=1)
    (g : Coloring (m*3) (m*3)) : ∃ L : Layout m (Fin (m*3)), ∀ i c,
      let S : Finset _ := {L (i,0),L (i,1),L (i,2)}
      ∃ x∈S, ∃ y∉S, g.paint x y=c := by
  classical
  obtain ⟨L,good⟩ := partition_unordered (SealedTriple g) 3 (sealed_degree g odd)
    (by omega) (by omega : 2≤m) (Fintype.equivOfCardEq (by simp [Slot]) : Layout m (Fin (m*3)))
  refine ⟨L,fun i c => ?_⟩
  have neq (j k : Slot) (h : j≠k) : L (i,j)≠L (i,k) := fun e => h (Prod.mk.inj (L.injective e)).2
  dsimp only
  by_contra! h
  exact good i ⟨by simp [neq 0 1 (by decide),neq 0 2 (by decide),neq 1 2 (by decide)],c,h⟩

#print axioms valid_triple_partition
end WildExact.TripleRepair
