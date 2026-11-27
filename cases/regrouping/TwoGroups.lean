import ExactModel
namespace WildExact.Regroup
open WildDeletion
variable {V P : Type} (E : V → V → Prop) (port : P → V)
def Draw (side : P → Bool) (x y : V) : Prop :=
  E x y ∨ ∃ i j, x=port i ∧ y=port j ∧ side i=side j

/-- Joining all ports temporarily reaches every vertex exactly when each
component of the fixed graph contains a port. -/
theorem merge_iff [Nonempty P] (sym : ∀ {x y},E x y → E y x) :
    Connected (Draw E port (fun _ => false)) ↔ ∀ x,∃ i,Walk E x (port i) := by
  classical
  let o : P := Classical.choice ‹Nonempty P›
  constructor
  · intro conn x
    have follow {a b : V} (path : Walk (Draw E port (fun _ => false)) a b)
        (start : ∃ i, Walk E a (port i)) : ∃ j,Walk E b (port j) := by
      induction path with
      | stay => exact start
      | step _ h ih =>
        rcases h with edge|⟨_,j,_,rfl,_⟩
        · obtain ⟨i,old⟩ := ih
          exact ⟨i,(Walk.step (.stay _) (sym edge)).join old⟩
        · exact ⟨j,.stay _⟩
    exact follow (conn (port o) x) ⟨o,.stay _⟩
  · intro available x y
    obtain ⟨i,xi⟩ := available x
    obtain ⟨j,yj⟩ := available y
    have lift {a b : V} (h : Walk E a b) : Walk (Draw E port (fun _ => false)) a b :=
      Walk.mapInto (E:=E) id (fun _ _ e => .step (.stay _) (Or.inl e)) h
    exact ((lift xi).join (.step (.stay _) (Or.inr ⟨i,j,rfl,rfl,rfl⟩))).join (lift (backwards sym yj))

/-- After erasing the wild edges in two groups, a proposed two-group redraw
works precisely when the merged layout works and a path in the fixed graph
has its ends on opposite sides of the proposed split. -/
theorem split_iff (sym : ∀ {x y},E x y → E y x) (side : P → Bool)
    (both : ∃ i j,side i≠side j) :
    Connected (Draw E port side) ↔ Connected (Draw E port (fun _ => false)) ∧
      ∃ i j,side i≠side j ∧ Walk E (port i) (port j) := by
  classical
  obtain ⟨left,right,diff⟩ := both
  letI : Nonempty P := ⟨left⟩
  have chain (i j : P) (eq : side i=side j) : Walk (Draw E port side) (port i) (port j) :=
    .step (.stay _) (Or.inr ⟨i,j,rfl,rfl,eq⟩)
  have lift {a b : V} (h : Walk E a b) : Walk (Draw E port side) a b :=
    Walk.mapInto (E:=E) id (fun _ _ e => .step (.stay _) (Or.inl e)) h
  constructor
  · intro conn
    have merged : Connected (Draw E port (fun _ => false)) := by
      intro x y
      apply (conn x y).mapInto id
      rintro a b (edge|⟨i,j,rfl,rfl,_⟩)
      · exact .step (.stay _) (Or.inl edge)
      · exact .step (.stay _) (Or.inr ⟨i,j,rfl,rfl,rfl⟩)
    refine ⟨merged,?_⟩
    apply Classical.byContradiction
    intro noCross
    have stays {x y : V} (w : Walk (Draw E port side) x y)
        (base : ∃ i,side i=side left ∧ Walk E (port i) x) :
        ∃ i,side i=side left ∧ Walk E (port i) y := by
      induction w with
      | stay => exact base
      | step _ edge ih =>
        obtain ⟨i,hi,wi⟩ := ih
        rcases edge with adj|⟨a,b,rfl,rfl,ab⟩
        · exact ⟨i,hi,.step wi adj⟩
        · have ia : side i=side a := by by_contra ne; exact noCross ⟨i,a,ne,wi⟩
          exact ⟨b,ab.symm.trans (ia.symm.trans hi),.stay _⟩
    obtain ⟨i,hi,path⟩ := stays (conn (port left) (port right)) ⟨left,rfl,.stay _⟩
    exact noCross ⟨i,right,fun eq => diff (hi.symm.trans eq),path⟩
  · rintro ⟨merged,i,j,different,path⟩ x y
    have available := (merge_iff E port sym).mp merged
    obtain ⟨u,wu⟩ := available x
    obtain ⟨v,wv⟩ := available y
    have middle : Walk (Draw E port side) (port u) (port v) := by
      by_cases same : side u=side v
      · exact chain _ _ same
      by_cases ui : side u=side i
      · have vj : side v=side j := by revert same ui different; cases side u <;> cases side v <;> cases side i <;> cases side j <;> decide
        exact ((chain _ _ ui).join (lift path)).join (chain _ _ vj.symm)
      · have uj : side u=side j ∧ side i=side v := by revert same ui different; cases side u <;> cases side v <;> cases side i <;> cases side j <;> decide
        exact ((chain _ _ uj.1).join (lift (backwards sym path))).join (chain _ _ uj.2)
    exact ((lift wu).join middle).join (lift (backwards sym wv))

#print axioms split_iff
end WildExact.Regroup
