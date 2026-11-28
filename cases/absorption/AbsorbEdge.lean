import RootContraction

namespace WildExact.Absorption
open Finset WildDeletion RootContraction

variable {n k : Nat}

noncomputable def piece (g : Coloring n k) (w : Lines n) (c : Fin k) (x : Fin n) : Finset (Fin n) := by
  classical exact univ.filter (Walk (Joined g w c) x)

noncomputable def pieces (g : Coloring n k) (w : Lines n) (c : Fin k) :=
  univ.image (piece g w c)

theorem mem_piece {g : Coloring n k} {w : Lines n} {c x y} :
    y∈piece g w c x ↔ Walk (Joined g w c) x y := by classical simp [piece]

private theorem self_mem (g : Coloring n k) (w : Lines n) (c x) : x∈piece g w c x :=
  mem_piece.mpr (.stay x)

theorem piece_eq {g : Coloring n k} {w : Lines n} {c x y} :
    piece g w c x=piece g w c y ↔ Walk (Joined g w c) x y := by
  constructor
  · intro eq
    apply mem_piece.mp
    rw [eq]
    exact self_mem _ _ _ _
  · intro h
    ext z
    simp only [mem_piece]
    exact ⟨fun p => (backwards (joined_symm _) h).join p,fun p => h.join p⟩

private theorem one {g : Coloring n k} {w : Lines n} {c} (h : (pieces g w c).card≤1) :
    Connected (Joined g w c) := by
  intro x y
  exact piece_eq.mp (card_le_one.mp h _ (mem_image_of_mem _ (mem_univ x)) _ (mem_image_of_mem _ (mem_univ y)))

private theorem two {g : Coloring n k} {w : Lines n} {c x y}
    (h : (pieces g w c).card≤2) (different : ¬Walk (Joined g w c) x y) (z : Fin n) :
    Walk (Joined g w c) x z ∨ Walk (Joined g w c) y z := by
  classical
  by_contra! bad
  have xy := fun e => different (piece_eq.mp e)
  have xz := fun e => bad.1 (piece_eq.mp e)
  have yz := fun e => bad.2 (piece_eq.mp e)
  let f := piece g w c
  have sub : {f x,f y,f z} ⊆ pieces g w c := by
    intro q hq
    simp only [mem_insert,mem_singleton] at hq
    rcases hq with rfl|rfl|rfl <;> exact mem_image_of_mem _ (mem_univ _)
  have hz := card_le_card sub
  have nx : f x∉({f y,f z} : Finset _) := fun h => (mem_insert.mp h).elim xy (fun m => xz (mem_singleton.mp m))
  have ny : f y∉({f z} : Finset _) := fun h => yz (mem_singleton.mp h)
  have count : ({f x,f y,f z} : Finset _).card=3 := by
    rw [card_insert_of_not_mem nx,card_insert_of_not_mem ny,card_singleton]
  omega

/-- In each color the old components of the two endpoints must cover all vertices.
This also applies to layouts with many split colors. -/
theorem repair_iff_cover (g : Coloring n n) (w : Lines n) (x y : Fin n) :
    Works g (repair w x y) ↔ ∀ c v,Walk (Joined g w c) x v ∨ Walk (Joined g w c) y v := by
  constructor
  · intro wins c v
    let P := fun b => Walk (Joined g w c) x b ∨ Walk (Joined g w c) y b
    have step {a b} (h : Joined g (repair w x y) c a b) (p : P a) : P b := by
      have old (edge : Joined g w c a b) : P b :=
        p.elim (fun h => Or.inl (.step h edge)) (fun h => Or.inr (.step h edge))
      rcases h with wild|paint
      · rcases repair_touch wild with was|⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact old (Or.inl was)
        · exact Or.inr (.stay _)
        · exact Or.inl (.stay _)
      · exact old (Or.inr paint)
    have follow {a b} (p : Walk (Joined g (repair w x y) c) a b) : P a → P b := by
      induction p with
      | stay => exact id
      | step _ e ih => exact fun h => step e (ih h)
    exact follow (wins c x v) (Or.inl (.stay _))
  · intro cover c
    have all (v : Fin n) : Walk (Joined g (repair w x y) c) x v :=
      (cover c v).elim lift_walk (fun h => (link g w c x y).join (lift_walk h))
    exact fun a b => (backwards (joined_symm _) (all a)).join (all b)

/-- A list of available ordinary vertices may exclude all easy cuts at once.
Only split colors impose a further restriction on the last endpoint. -/
theorem endpoint_iff (g : Coloring n n) (w : Lines n) (x y : Fin n) :
    Works g (repair w x y) ↔ ∀ c,(pieces g w c).card≤2 ∧
      (Connected (Joined g w c) ∨ y∉piece g w c x) := by
  classical
  rw [repair_iff_cover]
  constructor
  · intro cover c
    have sub : pieces g w c⊆{piece g w c x,piece g w c y} := by
      intro S hs
      obtain ⟨v,_,rfl⟩ := mem_image.mp hs
      rcases cover c v with h|h
      · exact mem_insert.mpr (Or.inl (piece_eq.mpr h).symm)
      · exact mem_insert.mpr (Or.inr (mem_singleton.mpr (piece_eq.mpr h).symm))
    refine ⟨(card_le_card sub).trans ((card_insert_le _ _).trans_eq (by simp)),?_⟩
    by_cases h : y∈piece g w c x
    · have all (v) : Walk (Joined g w c) x v :=
        (cover c v).elim id (fun p => (mem_piece.mp h).join p)
      exact Or.inl fun a b => (backwards (joined_symm _) (all a)).join (all b)
    · exact Or.inr h
  · intro conditions c v
    obtain ⟨size,conn|outside⟩ := conditions c
    · exact Or.inl (conn x v)
    · exact two size (fun h => outside (mem_piece.mpr h)) v

#print axioms endpoint_iff

/-- The reserved color isolates the small block. Its outside can be repaired simultaneously
with one other two-component color, by choosing the endpoint after the layout is known. -/
theorem absorb (g : Coloring n n) (w : Lines n) (leg : Legal w) (base : Fin n) (special : Fin n)
    (A : Finset (Fin n)) (proper : A≠univ) (reserved : piece g w special base=A)
    (block : ∀ c, A⊆piece g w c base)
    (budget : 2*((pieces g w special).card-2)+
      ∑ c∈univ.erase special,((pieces g w c).card-1)≤1) :
    ∃ y∉A, Legal (repair w base y) ∧ (repair w base y).card≤w.card+1 ∧ Works g (repair w base y) := by
  classical
  let d (c : Fin n) := (pieces g w c).card-1
  have total : (∑ c∈univ.erase special,d c)≤1 := by dsimp [d]; omega
  have sp : (pieces g w special).card≤2 := by omega
  have outside : ∃ y,y∉A := by
    by_contra! h
    exact proper (eq_univ_of_forall h)
  have choosePoint : ∃ y∉A, ∀ c,c≠special → ∀ x,Walk (Joined g w c) base x ∨ Walk (Joined g w c) y x := by
    by_cases finished : ∀ c,c≠special → Connected (Joined g w c)
    · obtain ⟨y,hy⟩ := outside
      exact ⟨y,hy,fun c ne x => Or.inl (finished c ne _ x)⟩
    push_neg at finished
    obtain ⟨c,ne,no⟩ := finished
    have m : c∈univ.erase special := mem_erase.mpr ⟨ne,mem_univ _⟩
    have dc : 1≤d c := by
      by_contra! h
      exact no (one (by dsimp [d] at h; omega))
    have eq := sum_erase_add (univ.erase special) d m
    have dc' : (pieces g w c).card≤2 := by dsimp [d] at *; omega
    have missing : ∃ y, ¬Walk (Joined g w c) base y := by
      by_contra! all
      exact no (fun x y => (backwards (joined_symm _) (all x)).join (all y))
    obtain ⟨y,hy⟩ := missing
    refine ⟨y,fun inA => hy (mem_piece.mp (block c inA)),?_⟩
    intro col other x
    by_cases eqc : col=c
    · exact eqc ▸ two dc' hy x
    · have incl : col∈(univ.erase special).erase c := by simp [other,eqc]
      have val := single_le_sum (f:=d) (fun i _ => Nat.zero_le (d i)) incl
      have small : (pieces g w col).card≤1 := by dsimp [d] at val; dsimp [d] at *; omega
      exact Or.inl (one small _ x)
  obtain ⟨y,hy,other⟩ := choosePoint
  refine ⟨y,hy,repair_legal leg _ _,repair_size _ _ _,?_⟩
  intro c
  have both (x : Fin n) : Walk (Joined g w c) base x ∨ Walk (Joined g w c) y x := by
    by_cases eq : c=special
    · subst c
      apply two sp _ _
      intro h
      exact hy (reserved ▸ mem_piece.mpr h)
    · exact other c eq x
  have all (x : Fin n) : Walk (Joined g (repair w base y) c) base x :=
    (both x).elim lift_walk (fun p => (link g w c base y).join (lift_walk p))
  exact fun x z => (backwards (joined_symm _) (all x)).join (all z)

#print axioms absorb
end WildExact.Absorption
