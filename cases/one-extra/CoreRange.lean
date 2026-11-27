import TwoGroupCore
namespace WildCuts.OneExtra
open Finset WildExact WildDeletion

/-- A graph-level target for choosing a split. The unused part of the edge
budget is enough for a star on each half of the core. -/
def SmallCore {n k : Nat} (g : Coloring n k) (limit : Nat) :=
  ∃ (R : Finset (Fin n)) (w : Lines n),6≤R.card ∧ R.card≤8 ∧ Legal w ∧
    w.card+(R.card-2)≤limit ∧ MeetsCore g w R

theorem lift_meets {n : Nat} (g : Coloring (n+1) n) {R : Finset (Fin n)} {w : Lines n}
    (old : MeetsCore (restrict g) w R) :
    MeetsCore g (w.map liftLine) (R.map (Fin.castLEEmb (Nat.le_succ n))) := by
  let Q := R.map (Fin.castLEEmb (Nat.le_succ n))
  let u := w.map liftLine
  intro c
  have lift (x : Fin n) : ∃ y∈Q,Walk (Joined g u c) x.castSucc y := by
    obtain ⟨y,hy,walk⟩ := old c x
    refine ⟨y.castSucc,mem_map.mpr ⟨y,hy,rfl⟩,Walk.mapInto Fin.castSucc ?_ walk⟩
    intro l r hit
    apply Walk.step (.stay _)
    rcases hit with (a|a)|⟨ne,eq⟩
    · exact Or.inl (Or.inl (mem_map.mpr ⟨_,a,rfl⟩))
    · exact Or.inl (Or.inr (mem_map.mpr ⟨_,a,rfl⟩))
    · exact Or.inr ⟨(Fin.castSucc_injective n).ne ne,eq⟩
  intro x
  refine Fin.lastCases ?_ lift x
  let col (v : Fin n) := g.paint (Fin.last n) v.castSucc
  have inj : Function.Injective col := fun v z eq => Fin.castSucc_injective n
    (g.proper _ _ _ (Fin.ne_of_gt (Fin.castSucc_lt_last _)) (Fin.ne_of_gt (Fin.castSucc_lt_last _)) eq)
  obtain ⟨v,eq⟩ := (Finite.injective_iff_surjective.mp inj) c
  obtain ⟨y,hy,path⟩ := lift v
  have edge : Joined g u c (Fin.last n) v.castSucc := Or.inr ⟨Fin.ne_of_gt (Fin.castSucc_lt_last _),eq⟩
  exact ⟨y,hy,(Walk.step (.stay _) edge).join path⟩

private theorem lift_core {n b : Nat} (g : Coloring (n+1) n) (h : SmallCore (restrict g) b) :
    SmallCore g b := by
  obtain ⟨R,w,lo,hi,legal,budget,old⟩ := h
  let embed := Fin.castLEEmb (Nat.le_succ n)
  let Q := R.map embed
  let u := w.map liftLine
  have size : Q.card=R.card := card_map _
  refine ⟨Q,u,size ▸ lo,size ▸ hi,?_,?_,?_⟩
  · intro e he
    obtain ⟨f,hf,rfl⟩ := mem_map.mp he
    exact legal f hf
  · simpa only [u,card_map,size] using budget
  exact lift_meets g old

/-- Every coloring of every size from 15 through 82 has an exterior shared
by all colors with a core of at most eight vertices at the target budget. -/
theorem small_core_pair (n : Nat) (lo : 15≤n) (hi : n≤81) (odd : n%2=1) :
    (∀ g : Coloring n n,SmallCore g ((2*n+2)/3)) ∧
    (∀ g : Coloring (n+1) n,SmallCore g ((2*n+2)/3)) := by
  have h (g : Coloring n n) : SmallCore g ((2*n+2)/3) := by
    obtain ⟨i,lt,rfl⟩ : ∃ i,i<34 ∧ n=order i := ⟨(n-15)/2,by omega,by dsimp [order];omega⟩
    obtain ⟨p,U,_,size,legal,cost,reach⟩ := two_group_reduction i lt g
    refine ⟨_,_,?_,?_,legal,cost,reach⟩ <;> rw [size] <;> split <;> omega
  exact ⟨h,fun g => lift_core g (h (restrict g))⟩

#print axioms small_core_pair
end WildCuts.OneExtra
