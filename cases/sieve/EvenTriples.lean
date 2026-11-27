import GraphSieve
namespace WildSieve.EvenTriples
open Finset WildExact WildDeletion
local instance (priority := 2000) pureFinEq {m : Nat} : DecidableEq (Fin m) :=
  (inferInstance : LinearOrder (Fin m)).toDecidableEq
variable {A C : Type} [LinearOrder A] [Fintype A] [Fintype C]

/-- At equal sizes it is sufficient to check the side avoiding one fixed vertex. -/
def available (r : A) (t j : Nat) : Finset A := if 2*j=t then univ.erase r else univ

noncomputable def cuts (F : Factor A C) (r : A) (t j : Nat) :=
  sides F ∅ (available r t j) (3*j)

theorem cut_size (F : Factor A C) (r : A) (t j : Nat) (X : Finset A) (hx : X∈cuts F r t j) :
    X.card=3*j := by
  obtain ⟨c,mem⟩ := side_mem.mp hx
  exact (candidate_mem.mp mem).2.1

def pureDegree (n _t u j : Nat) := improvedDegree (n-1) n 0 0 (3*j) u

def pureTotal (n t j : Nat) := if (3*j)%2=0 then
  (n-1)*((n/2-(if 2*j=t then 1 else 0)).choose (3*j/2)) else 0

theorem pure_local (F : Factor A C) (r : A) (t j : Nat) (U : Finset A) (z : A) (hz : z∈U)
    (n : Nat) (pts : Fintype.card A=n) (cols : Fintype.card C=n-1) :
    (active (cuts F r t j) U z).card≤pureDegree n t U.card j := by
  have sub : active (cuts F r t j) U z⊆(sides F ∅ U (3*j)).filter (fun X => z∈X) := by
    intro X hx
    obtain ⟨h,xu,zx⟩ := mem_filter.mp hx
    obtain ⟨c,hc⟩ := side_mem.mp h
    obtain ⟨_,sz,cl⟩ := candidate_mem.mp hc
    exact mem_filter.mpr ⟨side_mem.mpr ⟨c,candidate_mem.mpr ⟨xu,sz,cl⟩⟩,zx⟩
  have rain : Rainbow F ∅ := fun c => by simp [Inside,lowerEnds]
  have bound := sides_local_improved F ∅ ∅ U (3*j) z hz rain Subset.rfl (by simp)
  simpa [pureDegree,pts,cols] using (card_le_card sub).trans bound

theorem pure_global (F : Factor A C) (r : A) (t j n : Nat)
    (pts : Fintype.card A=n) (cols : Fintype.card C=n-1) :
    (cuts F r t j).card≤pureTotal n t j := by
  classical
  let V := available r t j
  let fam (c : C) := candidates F c ∅ V (3*j)
  have per (c : C) : (fam c).card≤if (3*j)%2=0 then
      (n/2-(if 2*j=t then 1 else 0)).choose (3*j/2) else 0 := by
    have data (X) (hx : X∈fam c) : X⊆V ∧ X.card=3*j ∧ Closed (F.f c) X := by
      simpa only [empty_union] using candidate_mem.mp hx
    split
    next even =>
      have h := count_free (F.invol c) (F.moving c) V ∅ (fam c) (3*j) (by
        intro X hx
        obtain ⟨sub,sz,cl⟩ := data X hx
        exact ⟨sub,sz,empty_subset _,by simpa using cl⟩)
      simp only [card_empty,Nat.sub_zero,sdiff_empty] at h
      apply h.trans
      apply Nat.choose_le_choose
      have full := closed_size (F.invol c) (F.moving c) (show Closed (F.f c) univ from fun x _ => mem_univ _)
      rw [card_univ,pts] at full
      by_cases tie : 2*j=t
      · have raw := ends_bound (F.invol c) (univ.erase r)
        rw [card_erase_of_mem (mem_univ _),card_univ,pts] at raw
        simp only [V,available,if_pos tie]
        omega
      · simp only [V,available,if_neg tie,Nat.sub_zero]
        omega
    next odd =>
      by_contra! pos
      obtain ⟨X,hX⟩ := card_pos.mp pos
      obtain ⟨_,sz,cl⟩ := data X hX
      have pc := closed_size (F.invol c) (F.moving c) cl
      omega
  have all := (card_biUnion_le (s:=univ) (t:=fam)).trans (sum_le_sum (s:=univ) (fun c _ => per c))
  by_cases parity : (3*j)%2=0 <;> simpa [cuts,sides,fam,pureTotal,nsmul_eq_mul,parity,cols,V] using all

variable {n : Nat}

private theorem block_cut {A : Type} [LinearOrder A] [Fintype A]
    (L : Layout (univ : Finset A)) (S : Finset A) (whole : ∀ T∈L.val,Cohesive T S) :
    ∃ M : Layout S,M.val⊆L.val := by
  classical
  let M := L.val.filter (fun T => (T∩S).Nonempty)
  refine ⟨⟨M,L.property.1.sub (filter_subset _ _),?_⟩,filter_subset _ _⟩
  ext x
  constructor
  · intro h
    obtain ⟨T,ht,xt⟩ := mem_biUnion.mp h
    obtain ⟨tl,y,yt⟩ := mem_filter.mp ht
    exact whole T tl y (mem_inter.mp yt).1 x xt (mem_inter.mp yt).2
  · intro xs
    obtain ⟨T,tl,xt⟩ := mem_biUnion.mp (show x∈vertices L.val by rw [L.property.2]; simp)
    exact mem_biUnion.mpr ⟨T,mem_filter.mpr ⟨tl,x,mem_inter.mpr ⟨xt,xs⟩⟩,xt⟩

/-- When all vertices are in triples, an even coloring needs only
matching cuts of even size. Every triple costs two ordinary wild edges. -/
theorem pure_upper (g : Coloring (n+1) n) (r : Fin (n+1)) (t : Nat) (size : n+1=3*t)
    (L : Layout (univ : Finset (Fin (n+1)))) (pass : ∀ j∈shortLevels∪longLevels t,
      ∀ X∈cuts (coloringFactor g) r t j,L∉sealEvent X) : Upper g (2*t) := by
  classical
  let w := L.val.biUnion spokes
  have num := L.property.1.card_vertices
  rw [L.property.2,card_univ,Fintype.card_fin] at num
  have count : L.val.card=t := by omega
  refine ⟨w,?_,?_,?_⟩
  · intro e he
    obtain ⟨T,_,h⟩ := mem_biUnion.mp he
    exact spokes_legal T e h
  · apply card_biUnion_le.trans
    calc
      _ ≤ ∑ _∈L.val,2 := sum_le_sum fun T ht => (spokes_bound T).trans (by rw [L.property.1.size _ ht])
      _ = _ := by simp [count,Nat.mul_comm]
  intro c x y
  by_contra lost
  let F := coloringFactor g
  let S := univ.filter fun v => Walk (Joined g w c) x v
  have ins (v) : v∈S ↔ Walk (Joined g w c) x v := by simp [S]
  have whole (T) (ht : T∈L.val) : Cohesive T S := by
    intro a ha b hb sa
    apply (ins b).mpr
    apply ((ins a).mp sa).join
    apply Walk.mapInto (E:=Touch w) id (fun _ _ h => .step (.stay _) (Or.inl h))
    exact in_star (fun e he => mem_biUnion.mpr ⟨T,ht,he⟩) ha hb
  have cl : Closed (F.f c) S := fun v hv => (ins _).mpr
    (Walk.step ((ins _).mp hv) (Or.inr (mate_spec g c v)))
  have pos : S.Nonempty := ⟨x,(ins _).mpr (.stay _)⟩
  have neg : Sᶜ.Nonempty := ⟨y,mem_compl.mpr (fun h => lost ((ins _).mp h))⟩
  have forbid (Q : Finset (Fin (n+1))) (qpos : Q.Nonempty) (qc : Closed (F.f c) Q)
      (qw : ∀ T∈L.val,Cohesive T Q) (small : 2*Q.card≤n+1) (orient : 2*Q.card=n+1 → r∉Q) : False := by
    obtain ⟨M,sub⟩ := block_cut L Q qw
    let j := M.val.card
    have qsz := M.property.1.card_vertices
    rw [M.property.2] at qsz
    change Q.card=3*j at qsz
    have jpos := card_pos.mpr qpos
    have level : j∈shortLevels∪longLevels t := by
      by_cases e : j=1 ∨ j=2
      · exact mem_union_left _ (by simpa only [shortLevels,mem_insert,mem_singleton] using e)
      · exact mem_union_right _ (mem_filter.mpr ⟨mem_range.mpr (by omega),by omega⟩)
    have vsub : Q⊆available r t j := by
      by_cases tie : 2*j=t
      · simp only [available,if_pos tie]
        exact fun v hv => mem_erase.mpr ⟨fun eq => orient (by omega) (eq ▸ hv),mem_univ _⟩
      · simp [available,tie]
    exact pass j level Q (side_mem.mpr ⟨c,candidate_mem.mpr ⟨vsub,qsz,by simpa using qc⟩⟩)
      (mem_seal.mpr ⟨M,sub⟩)
  have sz : Sᶜ.card=n+1-S.card := by rw [card_compl,Fintype.card_fin]
  have bound := S.card_le_univ
  simp only [Fintype.card_fin] at bound
  by_cases takeS : 2*S.card<n+1 ∨ (2*S.card=n+1 ∧ r∉S)
  · apply forbid S pos cl whole (by omega)
    intro eq
    exact (takeS.resolve_left (by omega)).2
  · refine forbid Sᶜ neg ?_ (fun T ht => (whole T ht).complement) (by omega) ?_
    · intro v hv
      apply mem_compl.mpr
      intro h
      exact mem_compl.mp hv (F.invol c v ▸ cl _ h)
    · intro tie rr
      have nz := mem_compl.mp rr
      exact takeS (Or.inr ⟨by omega,nz⟩)
end WildSieve.EvenTriples
