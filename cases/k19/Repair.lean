import EdgeWalk
namespace K19Repair
open WildDeletion EdgeWalk
private theorem enlarge {n} (w : List (Edge n)) (m : List (Edge n)) (a b : Fin n)
    {x y : Fin n} (h : Walk (Adj (w++m)) x y) :
    Walk (Adj (((a,b)::w)++m)) x y := by
  apply Walk.mapInto (fun v => v) (E := Adj (w++m)) (F := Adj (((a,b)::w)++m)) _ h
  intro u v edge
  apply Walk.step (.stay u)
  rcases edge with e | e
  · exact Or.inl (List.mem_cons_of_mem _ e)
  · exact Or.inr (List.mem_cons_of_mem _ e)

/-- If all remaining pieces can reach one of a,b and be reached back from it,
one additional ordinary wild edge suffices. -/
theorem last_edge {n : Nat} {C : Type} [DecidableEq C] (m : C → List (Edge n)) (w : List (Edge n))
    (c : C) (a b : Fin n) (old : ∀ k, k ≠ c → Connected (Adj (w++m k)))
    (two : ∀ v, (Walk (Adj (w++m c)) v a ∧ Walk (Adj (w++m c)) a v) ∨
      (Walk (Adj (w++m c)) v b ∧ Walk (Adj (w++m c)) b v)) :
    ∀ k, Connected (Adj (((a,b)::w)++m k)) := by
  intro k
  by_cases he : k = c
  · subst k
    have ab : Walk (Adj (((a,b)::w)++m c)) a b :=
      .step (.stay _) (Or.inl (by simp))
    have ba : Walk (Adj (((a,b)::w)++m c)) b a :=
      .step (.stay _) (Or.inr (by simp))
    have both (v : Fin n) : Walk (Adj (((a,b)::w)++m c)) v a ∧
        Walk (Adj (((a,b)::w)++m c)) a v := by
      rcases two v with ⟨va,av⟩ | ⟨vb,bv⟩
      · exact ⟨enlarge _ _ _ _ va,enlarge _ _ _ _ av⟩
      · exact ⟨(enlarge _ _ _ _ vb).join ba, ab.join (enlarge _ _ _ _ bv)⟩
    exact fun x y => (both x).1.join (both y).2
  · exact fun x y => enlarge _ _ _ _ (old k he x y)
#print axioms last_edge
end K19Repair
