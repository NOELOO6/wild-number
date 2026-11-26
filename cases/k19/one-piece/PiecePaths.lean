import GroupMerges
namespace WildPieces
open Finset WildCuts EdgeWalk WildDeletion
def stars (p : Equiv.Perm V) := (wild groups19 p).map ordered

private theorem same_edge (a b : Edge 19) (h : ordered a = ordered b) : a=b ∨ a=b.swap := by
  rcases a with ⟨i,j⟩
  rcases b with ⟨u,v⟩
  by_cases h₁ : i≤j <;> by_cases h₂ : u≤v <;> simp [ordered,h₁,h₂,Prod.ext_iff] at h ⊢
  · exact Or.inl h
  · exact Or.inr h
  · exact Or.inr h.symm
  · exact Or.inl h.symm

theorem stars_properties (p : Equiv.Perm V) : (stars p).Nodup ∧
    (∀ e ∈ stars p, e.1 < e.2) ∧ (stars p).length = 13 := by
  let left := (List.finRange 19).filter fun x => x != groups19.rep (groups19.tag x)
  have fresh (x : V) (hx : x ∈ left) (j : G) : x ≠ groups19.rep j := by
    have h := (List.mem_filter.mp hx).2
    intro eq
    subst x
    simp [groups19.section_] at h
  constructor
  · unfold stars wild
    rw [List.map_map]
    apply List.Nodup.map_on _ ((List.nodup_finRange 19).filter _)
    intro x hx y _ eq
    rcases same_edge _ _ eq with dir | rev
    · exact p.injective (congrArg Prod.fst dir)
    · exact (fresh x hx _ (p.injective (congrArg Prod.fst rev))).elim
  constructor
  · intro x hx
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hx
    have ne := wild_simple groups19 p e he
    unfold ordered
    split
    · exact lt_of_le_of_ne ‹_› ne
    · exact lt_of_not_ge ‹_›
  · simp only [stars,wild,List.length_map]
    decide

private theorem reversePath {es : List (Edge 19)} {x y} (h : Walk (Adj es) x y) : Walk (Adj es) y x := by
  induction h with
  | stay => exact .stay _
  | step _ e ih => exact (Walk.step (E:=Adj es) (.stay _) e.symm).join ih

def hub (p : Equiv.Perm V) (i : G) := p.symm (groups19.rep i)
private theorem inside (p : Equiv.Perm V) (m : List (Edge 19)) (v : V) :
    Walk (Adj (stars p.symm ++ m)) v (hub p (groups19.tag (p v))) := by
  let x := p v
  let r := groups19.rep (groups19.tag x)
  by_cases eq : x=r
  · have e : v = hub p (groups19.tag (p v)) := by simpa [x,r,hub] using congrArg p.symm eq
    rw [← e]; exact .stay _
  have edge : (p.symm x,p.symm r) ∈ wild groups19 p.symm := by
    apply List.mem_map_of_mem (f:=fun t => (p.symm t,p.symm (groups19.rep (groups19.tag t))))
    simp [eq,x,r] at *
  have mem := List.mem_append_left m (List.mem_map_of_mem (f:=ordered) edge)
  have h : Adj (stars p.symm ++ m) (p.symm x) (p.symm r) := by
    by_cases le : p.symm x ≤ p.symm r
    · exact Or.inl (by simpa [stars,ordered,le] using mem)
    · exact Or.inr (by simpa [stars,ordered,le] using mem)
  exact Walk.step (.stay v) (by simpa [x,r,hub] using h)

theorem actual_paths (p q : Equiv.Perm V) (m : List (Edge 19))
    (colored : ∀ x, x ≠ (pairs 19).rep ((pairs 19).tag x) →
      Adj m (q x) (q ((pairs 19).rep ((pairs 19).tag x)))) (x y : V)
    (same : components (p*q) (groups19.tag (p x)) = components (p*q) (groups19.tag (p y))) :
    Walk (Adj (stars p.symm ++ m)) x y := by
  let E := Adj (stars p.symm ++ m)
  have eqR : Equivalence (Walk E) := ⟨fun z => Walk.stay z,fun h => reversePath h,fun a b => a.join b⟩
  have crossings (e : G×G) (he : e ∈ links (p*q)) : Walk E (hub p e.1) (hub p e.2) := by
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp he
    let u := (pairs 19).rep ((pairs 19).tag t)
    have step : Walk E (q t) (q u) := by
      by_cases eq : t=u
      · rw [eq]; exact .stay _
      apply Walk.step (.stay _)
      rcases colored t eq with ok | ok
      · exact Or.inl (List.mem_append_right _ ok)
      · exact Or.inr (List.mem_append_right _ ok)
    exact (reversePath (inside p m (q t))).join (step.join (inside p m (q u)))
  have lift := finish_congr _ eqR (hub p) id (links (p*q)) (fun i j (h : i=j) => h ▸ eqR.refl _) crossings
  exact (inside p m x).join ((lift _ _ same).join (reversePath (inside p m y)))
end WildPieces
