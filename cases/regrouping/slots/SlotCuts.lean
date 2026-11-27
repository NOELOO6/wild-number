import UniversalLower

namespace WildSlots
open WildDeletion WildExact Finset

variable {V I C : Type}

/-- Add an undirected edge between each allowed point and destination. -/
def links (u v : I → V) (allow : I → I → Prop) (x y : V) :=
  ∃ i j,allow i j ∧ ((x=u i ∧ y=v j) ∨ (y=u i ∧ x=v j))

def extend (E : V → V → Prop) (u v : I → V) (allow : I → I → Prop) (x y : V) :=
  E x y ∨ links u v allow x y

def passes (E : C → V → V → Prop) (u v : I → V) (allow : I → I → Prop) :=
  ∀ c,Connected (extend (E c) u v allow)

def assign (p : Equiv.Perm I) (i j : I) := p i=j

theorem extend_symm {E : V → V → Prop} (sym : ∀ {x y},E x y → E y x)
    {u v : I → V} {allow} {x y} : extend E u v allow x y → extend E u v allow y x := by
  rintro (e|⟨i,j,ok,h⟩)
  · exact Or.inl (sym e)
  · exact Or.inr ⟨i,j,ok,h.symm⟩

theorem passes_mono {E : C → V → V → Prop} {u v : I → V} {P Q : I → I → Prop}
    (sub : ∀ i j,P i j → Q i j) (yes : passes E u v P) : passes E u v Q := by
  intro c x y
  apply Walk.mapInto id _ (yes c x y)
  intro a b h
  apply Walk.step (.stay _)
  rcases h with e|⟨i,j,p,edge⟩
  · exact Or.inl e
  · exact Or.inr ⟨i,j,sub _ _ p,edge⟩

theorem constant_on_walk {E : V → V → Prop} {f : V → Bool}
    (keep : ∀ x y,E x y → f x=f y) {a b} (w : Walk E a b) : f a=f b := by
  induction w with
  | stay => rfl
  | step _ e ih => exact ih.trans (keep _ _ e)

private theorem cut_test {E : V → V → Prop} (sym : ∀ {x y}, E x y → E y x) :
    Connected E ↔ ∀ f : V → Bool,(∀ x y,E x y → f x=f y) → ∀ x y,f x=f y := by
  classical
  constructor
  · exact fun h _ keep x y => constant_on_walk keep (h x y)
  · intro all x y
    let f (v : V) := decide (Walk E x v)
    have keep (a b) (e : E a b) : f a=f b :=
      Bool.eq_iff_iff.mpr (by simp only [f,decide_eq_true_eq];exact
        ⟨fun h => .step h e,fun h => .step h (sym e)⟩)
    have equal := all f keep x y
    exact of_decide_eq_true (equal.symm.trans (show f x=true from decide_eq_true (Walk.stay x)))

/-- It suffices to test larger sets of links whenever every possible pattern
of cut sides on the movable points is respected by at least one test. -/
theorem pass_from_tests {T : Type} (E : C → V → V → Prop)
    (sym : ∀ c {x y},E c x y → E c y x) (u v : I → V) (p : Equiv.Perm I)
    (test : T → I → I → Prop)
    (cover : ∀ f : I → Bool,∃ t,∀ i j,test t i j → f i=f (p.symm j))
    (good : ∀ t,passes E u v (test t)) : passes E u v (assign p) := by
  intro c
  apply (cut_test (E:=extend (E c) u v (assign p)) (fun h => extend_symm (fun e => sym c e) h)).mpr
  intro f keep x y
  have paired (i : I) : f (u i)=f (v (p i)) :=
    keep _ _ (Or.inr ⟨i,p i,rfl,Or.inl ⟨rfl,rfl⟩⟩)
  obtain ⟨t,rule⟩ := cover (fun i => f (u i))
  apply constant_on_walk (E:=extend (E c) u v (test t)) _ (good t c x y)
  intro a b hit
  rcases hit with e|⟨i,j,ok,pos|neg⟩
  · exact keep a b (Or.inl e)
  · obtain ⟨rfl,rfl⟩ := pos
    simpa using (rule i j ok).trans (paired (p.symm j))
  · obtain ⟨rfl,rfl⟩ := neg
    simpa using ((rule i j ok).trans (paired (p.symm j))).symm

/-- An exact cut test for simultaneous reassignment of any number of points.
Each temporary graph allows every attachment that preserves one binary split. -/
theorem all_splits (E : C → V → V → Prop) (sym : ∀ c {x y},E c x y → E c y x)
    (u v : I → V) (p : Equiv.Perm I) :
    passes E u v (assign p) ↔ ∀ f : I → Bool,passes E u v (fun i j => f i=f (p.symm j)) := by
  constructor
  · intro h f
    exact passes_mono (fun i j (eq : p i=j) => by simp [←eq]) h
  · exact pass_from_tests E sym u v p _ (fun f => ⟨f,fun _ _ h => h⟩)

def edge {n : Nat} (a b : Fin n) : Fin n × Fin n := (min a b,max a b)
def draw {n : Nat} [Fintype I] (w : Lines n) (u v : I → Fin n) (p : Equiv.Perm I) :=
  w ∪ univ.image (fun i => edge (u i) (v (p i)))

private theorem touch_edge {n : Nat} (a b : Fin n) {x y : Fin n} :
    ((x,y)=edge a b ∨ (y,x)=edge a b) ↔ ((x=a ∧ y=b) ∨ (y=a ∧ x=b)) := by
  rcases le_total a b with le|le <;>
    simp [edge,min_eq_left,min_eq_right,max_eq_left,max_eq_right,le,Prod.mk.injEq,
      or_comm,and_comm]

theorem joined_draw {n k : Nat} [Fintype I] (g : Coloring n k) (w : Lines n)
    (u v : I → Fin n) (p : Equiv.Perm I) (c x y) :
    Joined g (draw w u v p) c x y ↔ extend (Joined g w c) u v (assign p) x y := by
  classical
  constructor
  · rintro ((hit|hit)|color)
    · rcases mem_union.mp hit with old|new
      · exact Or.inl (Or.inl (Or.inl old))
      obtain ⟨i,_,eq⟩ := mem_image.mp new
      exact Or.inr ⟨i,p i,rfl,(touch_edge ..).mp (Or.inl eq.symm)⟩
    · rcases mem_union.mp hit with old|new
      · exact Or.inl (Or.inl (Or.inr old))
      obtain ⟨i,_,eq⟩ := mem_image.mp new
      exact Or.inr ⟨i,p i,rfl,(touch_edge ..).mp (Or.inr eq.symm)⟩
    · exact Or.inl (Or.inr color)
  · rintro (((old|old)|color)|⟨i,j,(eq : p i=j),hit⟩)
    · exact Or.inl (Or.inl (mem_union_left _ old))
    · exact Or.inl (Or.inr (mem_union_left _ old))
    · exact Or.inr color
    subst j
    rcases (touch_edge ..).mpr hit with h|h
    · exact Or.inl (Or.inl (mem_union_right _ (mem_image.mpr ⟨i,mem_univ _,h.symm⟩)))
    · exact Or.inl (Or.inr (mem_union_right _ (mem_image.mpr ⟨i,mem_univ _,h.symm⟩)))

theorem works_draw {n k : Nat} [Fintype I] (g : Coloring n k) (w : Lines n)
    (u v : I → Fin n) (p : Equiv.Perm I) :
    Works g (draw w u v p) ↔ passes (Joined g w) u v (assign p) := by
  unfold Works passes
  simp_rw [show ∀ c,Joined g (draw w u v p) c=extend (Joined g w c) u v (assign p) from
    fun c => funext₂ (fun x y => propext (joined_draw g w u v p c x y))]

theorem upper_draw {n k : Nat} [Fintype I] (g : Coloring n k) (w : Lines n) (leg : Legal w)
    (u v : I → Fin n) (apart : ∀ i j,u i≠v j) (p : Equiv.Perm I)
    (pass : passes (Joined g w) u v (assign p)) : Upper g (w.card+Fintype.card I) := by
  refine ⟨draw w u v p,?_,?_,(works_draw g w u v p).mpr pass⟩
  · intro e he
    rcases mem_union.mp he with old|new
    · exact leg e old
    obtain ⟨i,_,rfl⟩ := mem_image.mp new
    rcases lt_or_gt_of_ne (apart i (p i)) with h|h
    · simpa [edge,min_eq_left h.le,max_eq_right h.le] using h
    · simpa [edge,min_eq_right h.le,max_eq_left h.le] using h
  · exact (card_union_le _ _).trans (Nat.add_le_add_left (card_image_le.trans_eq (card_univ : (univ : Finset I).card=Fintype.card I)) _)

#print axioms all_splits
end WildSlots
