import CutRepair

namespace WildCuts
open Finset EdgeWalk WildDeletion

/-- A named representative in each block, and the block of every point. -/
structure Blocks (V G : Type) where
  tag : V → G
  rep : G → V
  section_ : ∀ i, tag (rep i) = i

variable {n : Nat} {G H C : Type} [Fintype G] [DecidableEq G]
  [Fintype H] [DecidableEq H] [Fintype C] [DecidableEq C]
abbrev Points (n : Nat) := Fin n

def side (b : Blocks (Points n) G) (u : Finset G) : Finset (Points n) :=
  univ.filter (fun x => b.tag x ∈ u)
def wild (b : Blocks (Points n) G) (p : Equiv.Perm (Points n)) : List (Edge n) :=
  (((List.finRange n).filter (fun x => x != b.rep (b.tag x))).map
    (fun x => (p x, p (b.rep (b.tag x)))))

omit [Fintype G] [DecidableEq G] in
theorem wild_step (b : Blocks (Points n) G) (p : Equiv.Perm (Points n)) (x : Points n)
    (h : x ≠ b.rep (b.tag x)) : Adj (wild b p) (p x) (p (b.rep (b.tag x))) := by
  apply Or.inl
  apply List.mem_map_of_mem
  simp [h]

private theorem name_side (b : Blocks (Points n) G) (p : Equiv.Perm (Points n))
    (s : Finset (Points n))
    (h : ∀ x, p x ∈ s ↔ p (b.rep (b.tag x)) ∈ s) :
    (side b (univ.filter fun g => p (b.rep g) ∈ s)).map p.toEmbedding = s := by
  ext v
  rw [Finset.mem_map_equiv]
  simpa [side] using (h (p.symm v)).symm

abbrev SideName (G : Type) [Fintype G] [DecidableEq G] (root : G) :=
  {x : Finset G // x.Nonempty ∧ root ∉ x}

def cost (size n t : Nat) :=
  if size = t then size.factorial * (n-size).factorial else 0

omit [DecidableEq C] in
/-- A certificate for the number of cuts yields wild edges directly in the
graph. The color coordinates only name the pairs of each given matching. -/
theorem layout_and_repair [Nontrivial (Points n)]
    (b : Blocks (Points n) G) (d : Blocks (Points n) H) (root : G)
    (m : C → List (Edge n)) (q : C → Equiv.Perm (Points n))
    (colored : ∀ c x, x ≠ d.rep (d.tag x) → Adj (m c) (q c x) (q c (d.rep (d.tag x))))
    (budget : Fintype.card C *
      (∑ u : SideName G root, ∑ j : Finset H, cost (side b u.1).card n (side d j).card) <
      n.factorial * 3) :
    ∃ (p : Equiv.Perm (Points n)) (a z : Points n), a ≠ z ∧
      ∀ c, Connected (Adj (((a,z)::wild b p) ++ m c)) := by
  classical
  let I := C × SideName G root × Finset H
  let s : I → Finset (Points n) := fun i => side b i.2.1.1
  let t : I → Finset (Points n) := fun i => (side d i.2.2).map (q i.1).toEmbedding
  have fit : (∑ i : I, if (s i).card = (t i).card then
       (s i).card.factorial * (Fintype.card (Points n) - (s i).card).factorial else 0) <
       (Fintype.card (Points n)).factorial * 3 := by
    simpa [I,s,t,cost,Fintype.sum_prod_type] using budget
  obtain ⟨p,hp⟩ := choose_layout s t 3 fit
  let hit := univ.filter (fun i : I => (s i).map p.toEmbedding = t i)
  let r := p (b.rep root)
  have proper (i : I) : ((s i).map p.toEmbedding).Nonempty ∧ r ∉ (s i).map p.toEmbedding := by
    obtain ⟨g,hg⟩ := i.2.1.2.1
    refine ⟨⟨p (b.rep g),?_⟩,?_⟩
    · simp [s,side,Finset.mem_map_equiv,b.section_,hg]
    · simpa [r,s,side,Finset.mem_map_equiv,b.section_] using i.2.1.2.2
  obtain ⟨a,z,az,allCross⟩ := cross_all r hit (fun i => (s i).map p.toEmbedding) hp (fun i _ => proper i)
  refine ⟨p,a,z,az,fun c => connected_by_crossing _ _ r _ _ ?_⟩
  intro A nonempty outside inv
  have left (x : Points n) : p x ∈ A ↔ p (b.rep (b.tag x)) ∈ A := by
    by_cases eq : x = b.rep (b.tag x)
    · rw [← eq]
    have edge := wild_step b p x eq
    apply inv
    rcases edge with h | h
    · exact Or.inl (List.mem_append_left _ h)
    · exact Or.inr (List.mem_append_left _ h)
  have right (x : Points n) : q c x ∈ A ↔ q c (d.rep (d.tag x)) ∈ A := by
    by_cases eq : x = d.rep (d.tag x)
    · rw [← eq]
    apply inv
    rcases colored c x eq with h | h
    · exact Or.inl (List.mem_append_right _ h)
    · exact Or.inr (List.mem_append_right _ h)
  let u := univ.filter (fun i => p (b.rep i) ∈ A)
  let j := univ.filter (fun i => q c (d.rep i) ∈ A)
  have lu : (side b u).map p.toEmbedding = A := name_side b p A left
  have rj : (side d j).map (q c).toEmbedding = A := name_side d (q c) A right
  have hu : u.Nonempty := by
    obtain ⟨v,hv⟩ := nonempty
    refine ⟨b.tag (p.symm v),Finset.mem_filter.mpr ⟨Finset.mem_univ _,(left _).mp ?_⟩⟩
    simpa using hv
  have hr : root ∉ u := by simpa [u,r] using outside
  let i : I := (c,⟨u,hu,hr⟩,j)
  have yes : i ∈ hit := Finset.mem_filter.mpr ⟨Finset.mem_univ _,lu.trans rj.symm⟩
  have hc := allCross i yes
  change Cross ((side b u).map p.toEmbedding) a z at hc
  rwa [lu] at hc
end WildCuts
