import ThreeGroups
import StarDraw
namespace WildCuts.OneExtra
open Finset WildExact WildSieve WildDeletion EdgeWalk

private theorem three_connected (R : Fin 3 → Fin 3 → Prop) (refl : ∀ x,R x x)
    (sym : ∀ {x y},R x y → R y x) (trans : ∀ {x y z},R x y → R y z → R x z)
    (neighbor : ∀ x,∃ y,y≠x ∧ R x y) : ∀ x y,R x y := by
  intro x y
  by_cases xy : x=y
  · exact xy ▸ refl x
  obtain ⟨k,kx,hk⟩ := neighbor x
  obtain ⟨l,ly,hl⟩ := neighbor y
  by_cases ky : k=y
  · exact ky ▸ hk
  by_cases lx : l=x
  · exact lx ▸ sym hl
  have kl : k=l := by omega
  exact trans hk (kl ▸ sym hl)

def MeetsCore {n k : Nat} (g : Coloring n k) (w : Lines n) (R : Finset (Fin n)) :=
  ∀ c x,∃ y∈R,Walk (Joined g w c) x y

/-- A proposed group must have an old path, using its color and exterior
edges only, to a different group. -/
def Contacts {n k : Nat} (g : Coloring n k) (w : Lines n) (T : Fin 3 → Finset (Fin n)) :=
  ∀ c i,∃ j,j≠i ∧ ∃ x∈T i,∃ y∈T j,Walk (Joined g w c) x y

/-- Three non-isolated groups give a connected color. This produces legal
ordinary wild edges by drawing a star in each of the three groups. -/
theorem draw_three {n k : Nat} (g : Coloring n k) (w : Lines n) (legal : Legal w)
    (R : Finset (Fin n)) (reach : MeetsCore g w R) (T : Fin 3 → Finset (Fin n))
    (nonempty : ∀ i,(T i).Nonempty) (cover : ∀ x∈R,∃ i,x∈T i)
    (contacts : Contacts g w T) : Upper g (w.card+∑ i,((T i).card-1)) := by
  classical
  let stars := univ.biUnion (fun i => spokes (T i))
  let all := w∪stars
  have star (i) : spokes (T i)⊆all := fun _ h => mem_union_right _ (mem_biUnion.mpr ⟨i,mem_univ _,h⟩)
  refine ⟨all,?_,?_,?_⟩
  · intro e he
    rcases mem_union.mp he with h|h
    · exact legal e h
    obtain ⟨i,_,hit⟩ := mem_biUnion.mp h
    exact spokes_legal _ e hit
  · exact (card_union_le w stars).trans (Nat.add_le_add_left (card_biUnion_le.trans
      (sum_le_sum fun i _ => spokes_bound (T i))) _)
  intro c
  let E := Joined g all c
  have lift {x y} (h : Joined g w c x y) : E x y := by
    rcases h with (h|h)|col
    · exact Or.inl (Or.inl (mem_union_left _ h))
    · exact Or.inl (Or.inr (mem_union_left _ h))
    · exact Or.inr col
  have within {i x y} (hx : x∈T i) (hy : y∈T i) : Walk E x y :=
    Walk.mapInto (E:=Touch all) (F:=E) id (fun _ _ edge => .step (.stay _) (Or.inl edge)) (in_star (star i) hx hy)
  let rep (i) := (T i).min' (nonempty i)
  have member (i) : rep i∈T i := min'_mem _ _
  have connected := three_connected (fun i j => Walk E (rep i) (rep j))
    (fun _ => .stay _) (fun h => backwards (joined_symm g) h) (fun h k => h.join k) (by
      intro i
      obtain ⟨j,ji,x,hx,y,hy,link⟩ := contacts c i
      exact ⟨j,ji,((within (member i) hx).join
        (Walk.mapInto id (fun _ _ edge => .step (.stay _) (lift edge)) link)).join (within hy (member j))⟩)
  apply (complete_on_core (reach c) lift (joined_symm g)).mpr
  intro x hx y hy
  obtain ⟨i,hi⟩ := cover x hx
  obtain ⟨j,hj⟩ := cover y hy
  exact ((within hi (member i)).join (connected i j)).join (within (member j) hj)

def outsideStars {n t : Nat} (b : Blocks (Fin n) (Fin t)) (p : Equiv.Perm (Fin n))
    (U : Finset (Fin t)) := Uᶜ.biUnion (fun j => spokes (core b p {j}))

theorem exterior_reaches {n t : Nat} (g : Coloring n n) (b : Blocks (Fin n) (Fin t))
    (p : Equiv.Perm (Fin n)) (U : Finset (Fin t))
    (reach : ∀ c x,∃ y∈core b p U,Walk (Adj (exterior b p U++colorList g c)) x y) :
    MeetsCore g (outsideStars b p U) (core b p U) := by
  let w := outsideStars b p U
  have group {x j} : x∈core b p {j} ↔ b.tag (p.symm x)=j := by simp [in_core]
  have star {j} (hj : j∉U) : spokes (core b p {j})⊆w := fun _ hit =>
    mem_biUnion.mpr ⟨j,mem_compl.mpr hj,hit⟩
  intro c x
  obtain ⟨y,hy,walk⟩ := reach c x
  refine ⟨y,hy,Walk.mapInto id ?_ walk⟩
  have forward {v z : Fin n} (edge : (v,z)∈exterior b p U++colorList g c) :
      Walk (Joined g w c) v z := by
    rcases List.mem_append.mp edge with ext|col
    · obtain ⟨old,off⟩ := List.mem_filter.mp ext
      have nj : b.tag (p.symm v)∉U := of_decide_eq_true off
      have eq := same_block b p old
      exact Walk.mapInto (E:=Touch w) (F:=Joined g w c) id (fun _ _ h => .step (.stay _) (Or.inl h))
        (in_star (star nj) (group.mpr rfl) (group.mpr eq.symm))
    · exact .step (.stay _) (Or.inr ((list_color _ _ _ _).mp (Or.inl col)))
  intro v z edge
  exact edge.elim forward (fun h => backwards (joined_symm g) (forward h))

set_option maxHeartbeats 1000000
/-- A single exterior of cost twice the number of untouched triples works
for all colors. The graph inside the remaining set is still to be chosen. -/
theorem core_reduction (i : Nat) (small : i<34) (g : Coloring (order i) (order i)) :
    ∃ (p : Equiv.Perm (Fin (order i))) (U : Finset (Fin (regular i+1))),
      let R := core (template i) p U
      let w := outsideStars (template i) p U
      R.card=9+order i%3 ∧ Legal w ∧ w.card≤2*(regular i-2) ∧ MeetsCore g w R := by
  classical
  obtain ⟨p,U,three,root,size,reach⟩ := three_groups i small g
  let b := template i
  let w := outsideStars b p U
  refine ⟨p,U,size,?_,?_,?_⟩
  · intro e he
    obtain ⟨_,_,hit⟩ := mem_biUnion.mp he
    exact spokes_legal _ e hit
  · have each (j) (hj : j∈Uᶜ) : (spokes (core b p {j})).card≤2 := by
      have jr : j≠Fin.last (regular i) := fun eq => (mem_compl.mp hj) (eq ▸ root)
      have wid : width (template i) j=3 := (template_widths ⟨i,small⟩ j).trans (if_neg jr)
      apply (spokes_bound _).trans
      simp only [core,card_map,side_count,sum_singleton]
      change width (template i) j - 1 ≤ 2
      omega
    have le := (card_biUnion_le (s:=Uᶜ) (t:=fun j => spokes (core b p {j}))).trans
      (sum_le_sum fun j hj => each j hj)
    simpa [outsideStars,b,card_compl,three,Nat.mul_comm,Nat.sub_sub] using le
  exact exterior_reaches g b p U reach

/-- A simultaneous three-group test at the conjectured budget, valid for
all odd orders in the range and their even successors by restriction. -/
theorem exact_if_contacts {n : Nat} (hn : 3≤n) (g : Coloring n n) (w : Lines n)
    (legal : Legal w) (R : Finset (Fin n)) (reach : MeetsCore g w R)
    (T : Fin 3 → Finset (Fin n)) (nonempty : ∀ i,(T i).Nonempty)
    (cover : ∀ x∈R,∃ i,x∈T i) (contacts : Contacts g w T)
    (budget : w.card+(∑ i,((T i).card-1))≤(2*n+2)/3) : Exact g ((2*n+2)/3) := by
  obtain ⟨s,ls,cost,works⟩ := draw_three g w legal R reach T nonempty cover contacts
  apply exact_of_upper ⟨s,ls,cost.trans budget,works⟩
  intro u lu ok
  exact odd_lower hn g lu ok

#print axioms core_reduction
#print axioms exact_if_contacts
end WildCuts.OneExtra
