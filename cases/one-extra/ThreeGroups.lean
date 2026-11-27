import NearRange
namespace WildCuts.OneExtra
open Finset WildExact WildDeletion EdgeWalk

/-- The only retained wild edges are the original stars on the untouched triples. -/
def exterior {n t : Nat} (b : Blocks (Fin n) (Fin t)) (p : Equiv.Perm (Fin n)) (U : Finset (Fin t)) :=
  (wild b p).filter (fun e => decide (b.tag (p.symm e.1) ∉ U))

theorem same_block {n t : Nat} (b : Blocks (Fin n) (Fin t)) (p : Equiv.Perm (Fin n))
    {x y : Fin n} (h : (x,y) ∈ wild b p) : b.tag (p.symm x)=b.tag (p.symm y) := by
  obtain ⟨v,_,eq⟩ := List.mem_map.mp h
  cases eq
  simp [b.section_]

/-- Removing edges internal to a set leaves a path from every vertex to the
set whenever the original graph was connected. -/
private theorem reaches_set {V : Type} {E F : V → V → Prop} {R : V → Prop} {r : V}
    (base : R r) (paths : Connected E) (sym : ∀ {x y}, F x y → F y x)
    (keep : ∀ x y,E x y → F x y ∨ (R x ∧ R y)) (v : V) :
    ∃ y,R y ∧ Walk F v y := by
  have aux {x z} (walk : Walk E x z) : R x → ∃ y,R y ∧ Walk F z y := by
    induction walk with
    | stay => exact fun hx => ⟨_,hx,.stay _⟩
    | step w edge ih =>
      intro hx
      rcases keep _ _ edge with f|⟨_,hz⟩
      · obtain ⟨y,hy,prior⟩ := ih hx
        exact ⟨y,hy,(Walk.step (.stay _) (sym f)).join prior⟩
      · exact ⟨_,hz,.stay _⟩
  exact aux (paths r v) base

def core {n t : Nat} (b : Blocks (Fin n) (Fin t)) (p : Equiv.Perm (Fin n)) (U : Finset (Fin t)) :=
  (side b U).map p.toEmbedding

theorem in_core {n t : Nat} {b : Blocks (Fin n) (Fin t)} {p : Equiv.Perm (Fin n)}
    {U : Finset (Fin t)} {x : Fin n} : x∈core b p U ↔ b.tag (p.symm x)∈U := by
  simp [core,side,Finset.mem_map_equiv]

theorem strip {n t : Nat} (b : Blocks (Fin n) (Fin t)) (p : Equiv.Perm (Fin n))
    (U : Finset (Fin t)) {a z : Fin n} (ha : a∈core b p U) (hz : z∈core b p U)
    (m : List (Edge n)) (h : Connected (Adj (((a,z)::wild b p)++m))) (x : Fin n) :
    ∃ y∈core b p U,Walk (Adj (exterior b p U++m)) x y := by
  apply reaches_set ha h (fun e => e.symm) _ x
  have forward (v w : Fin n) (yes : (v,w)∈((a,z)::wild b p)++m) :
      Adj (exterior b p U++m) v w ∨ (v∈core b p U ∧ w∈core b p U) := by
    rcases List.mem_append.mp yes with yes|col
    · rcases List.mem_cons.mp yes with eq|star
      · cases eq;exact Or.inr ⟨ha,hz⟩
      · by_cases inside : b.tag (p.symm v)∈U
        · exact Or.inr ⟨in_core.mpr inside,in_core.mpr ((same_block b p star) ▸ inside)⟩
        · exact Or.inl (Or.inl (List.mem_append_left _ (List.mem_filter.mpr ⟨star,by simpa using inside⟩)))
    · exact Or.inl (Or.inl (List.mem_append_right _ col))
  intro v w edge
  rcases edge with yes|yes
  · exact forward v w yes
  · exact (forward w v yes).imp (fun e => e.symm) And.symm

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem template_widths : ∀ i : Fin 34,∀ j : Fin (regular i+1),
    width (template i) j=if j=Fin.last (regular i) then 3+order i%3 else 3 := by decide

/-- Every coloring in the range admits untouched exterior triples, common to
every color, with every vertex reaching the same 9-, 10-, or 11-point set. -/
theorem three_groups (i : Nat) (small : i<34) (g : Coloring (order i) (order i)) :
    ∃ (p : Equiv.Perm (Fin (order i))) (U : Finset (Fin (regular i+1))),
      U.card=3 ∧ Fin.last (regular i)∈U ∧
      (core (template i) p U).card=9+order i%3 ∧
      ∀ c x,∃ y∈core (template i) p U,
        Walk (Adj (exterior (template i) p U++colorList g c)) x y := by
  classical
  obtain ⟨p,a,z,_,connected⟩ := repaired_layout i small g
  let b := template i
  let r := Fin.last (regular i)
  let ga := b.tag (p.symm a)
  let gz := b.tag (p.symm z)
  let start : Finset (Fin (regular i+1)) := {ga,gz,r}
  have size : start.card≤3 := by
    have one := card_insert_le gz ({r} : Finset _)
    have two := card_insert_le ga ({gz,r} : Finset _)
    simp only [card_singleton] at one
    change (insert ga ({gz,r} : Finset (Fin (regular i+1)))).card≤3
    omega
  obtain ⟨U,cover,sz⟩ := exists_superset_card_eq size
    (show 3≤Fintype.card (Fin (regular i+1)) by simp [regular,order];omega)
  have root : r∈U := cover (by simp [start])
  have mema : a∈core b p U := in_core.mpr (cover (by change ga∈start;simp [start]))
  have memz : z∈core b p U := in_core.mpr (cover (by change gz∈start;simp [start]))
  refine ⟨p,U,sz,root,?_,fun c => strip b p U mema memz _ (connected c)⟩
  rw [core,card_map,side_count,← sum_erase_add U _ root]
  have sizes := template_widths ⟨i,small⟩
  have extSize : (∑ j∈U.erase r,width (template i) j)=(U.erase r).card*3 :=
    sum_const_nat fun j hj => (sizes j).trans (if_neg (mem_erase.mp hj).1)
  rw [extSize,card_erase_of_mem root,sz,sizes r,if_pos rfl]
  change 2*3+(3+order i%3)=9+order i%3
  omega

/-- Once the exterior is fixed, it suffices to connect the points of the
core for each color. The paths may use the exterior. -/
theorem complete_on_core {V : Type} {E F : V → V → Prop} {R : V → Prop}
    (reach : ∀ x,∃ y,R y ∧ Walk E x y) (includeE : ∀ {x y},E x y → F x y)
    (sym : ∀ {x y}, F x y → F y x) :
    Connected F ↔ ∀ x,R x → ∀ y,R y → Walk F x y := by
  refine ⟨fun h x _ y _ => h x y,?_⟩
  intro close a b
  obtain ⟨x,hx,ax⟩ := reach a
  obtain ⟨y,hy,by'⟩ := reach b
  have lift {u v} (h : Walk E u v) : Walk F u v :=
    Walk.mapInto id (fun _ _ e => .step (.stay _) (includeE e)) h
  exact ((lift ax).join (close x hx y hy)).join (backwards sym (lift by'))

#print axioms three_groups
#print axioms complete_on_core
end WildCuts.OneExtra
