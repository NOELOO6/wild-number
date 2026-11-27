import InnerCuts
import FrozenLayout

namespace WildSieve
open Finset
variable {A C : Type} [LinearOrder A] [Fintype A] [Fintype C]

def toFree (B S : Finset A) : Finset (Free B) := S.subtype (·∈Bᶜ)

theorem back_free {B S : Finset A} (sub : S⊆Bᶜ) :
    (toFree B S).map (emb B)=S := subtype_map_of_mem (fun _ h => sub h)

omit [Fintype A] in
theorem short_empty (B : Finset A) (r : A) (f t j) : ∅∈choices B r f t j := by simp [choices]
omit [Fintype A] in
theorem short_root (B : Finset A) (r : A) (f t j) : {r}∈choices B r f t j := by simp [choices]

/-- Six of the twelve points can be taken as three whole matching pairs. -/
theorem empty_twelve (F : Factor A C) (B : Finset A) (r : A) (f t : Nat)
    (X : Finset (Free B)) (hit : X∈pullSides F B ∅ 12) :
    (admissible shortLevels (badScopes F B r f t) X).card≤15300 := by
  classical
  obtain ⟨sz,c,cl⟩ := pull_mem.mp hit
  rw [empty_union] at cl
  let p := F.f c
  let S := X.map (emb B)
  have total := closed_size (F.invol c) (F.moving c) cl
  have ss : S.card=12 := by simpa only [S,card_map] using sz
  change S.card=2*(lowerEnds p S).card at total
  obtain ⟨E,sub,es⟩ := exists_subset_card_eq (s:=lowerEnds p S) (n:=3) (by omega)
  let Y := E ∪ E.image p
  have inS : Y⊆S := by
    intro x hx
    rcases mem_union.mp hx with h|h
    · exact (mem_filter.mp (sub h)).1
    obtain ⟨w,hw,rfl⟩ := mem_image.mp h
    exact (mem_filter.mp (sub hw)).2.2
  have dis : Disjoint E (E.image p) := by
    apply disjoint_left.mpr
    intro x hx hi
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hi
    have a := (mem_filter.mp (sub hx)).2.1
    rw [show p (p v)=v from F.invol c v] at a
    exact a.asymm (mem_filter.mp (sub hv)).2.1
  have ys : Y.card=6 := by
    rw [show Y=E ∪ E.image p from rfl,card_union_of_disjoint dis,card_image_of_injective _ (F.invol c).injective,es]
  have closed : Closed p Y := by
    intro x hx
    rcases mem_union.mp hx with h|h
    · exact mem_union_right _ (mem_image_of_mem p h)
    obtain ⟨v,hv,rfl⟩ := mem_image.mp h
    rw [show p (p v)=v from F.invol c v]
    exact mem_union_left _ hv
  have back := back_free (inS.trans (map_free B X))
  have small : (toFree B Y).card=6 := by rw [←card_map (f:=emb B),back,ys]
  apply trim_twelve shortLevels _ X (toFree B Y) sz small (map_subset_map.mp (back.symm ▸ inS)) (by decide)
  exact (mem_gather _ _ _).mpr ⟨∅,short_empty _ _ _ _ _,pull_mem.mpr ⟨small,c,by simpa [back] using closed⟩⟩

/-- The partner of the root belongs to the nine-point region. Joining that
point to each of the other four pairs gives four forbidden short triples. -/
theorem root_nine (F : Factor A C) (B : Finset A) (r : A) (f t : Nat) (rb : r∈B)
    (X : Finset (Free B)) (hit : X∈pullSides F B {r} 9) :
    (admissible shortLevels (badScopes F B r f t) X).card≤240 := by
  classical
  obtain ⟨sz,c,cl⟩ := pull_mem.mp hit
  let p := F.f c
  let S := X.map (emb B)
  let z := p r
  have rz : r≠z := F.moving c r
  have zS : z∈S := (mem_union.mp (cl r (mem_union_left _ (mem_singleton_self _)))).resolve_left (fun h => rz (mem_singleton.mp h).symm)
  have rS : r∉S := fun h => mem_compl.mp (map_free B X h) rb
  have pz : p z=r := F.invol c r
  let R := S.erase z
  have closed : Closed p R := by
    intro x hx
    obtain ⟨ne,xS⟩ := mem_erase.mp hx
    apply mem_erase.mpr
    constructor
    · exact fun eq => rS ((F.invol c).injective eq ▸ xS)
    · apply (mem_union.mp (cl x (mem_union_right _ xS))).resolve_left
      intro h
      exact ne ((F.invol c).injective ((mem_singleton.mp h).trans pz.symm))
  let E := lowerEnds p R
  have rs : R.card=8 := by rw [show R=S.erase z from rfl,card_erase_of_mem zS]; simp [S,sz]
  have four : E.card=4 := by
    have n := closed_size (F.invol c) (F.moving c) closed
    change R.card=2*E.card at n
    omega
  let Q (x : A) : Finset A := {z,x,p x}
  have props (x) (hx : x∈E) : x∈R ∧ p x∈R ∧ x<p x :=
    ⟨(mem_filter.mp hx).1,(mem_filter.mp hx).2.2,(mem_filter.mp hx).2.1⟩
  have inside (x) (hx : x∈E) : Q x⊆S := by
    obtain ⟨a,b,_⟩ := props x hx
    exact insert_subset zS (insert_subset (mem_erase.mp a).2 (singleton_subset_iff.mpr (mem_erase.mp b).2))
  have back (x) (hx : x∈E) := back_free ((inside x hx).trans (map_free B X))
  let freeQ (x : A) := toFree B (Q x)
  have eqQ : Set.InjOn freeQ E := by
    intro x hx y hy eq
    have same : Q x=Q y := (back x hx).symm.trans ((congrArg (Finset.map (emb B)) eq).trans (back y hy))
    have xy : x∈Q y := same ▸ mem_insert_of_mem (mem_insert_self _ _)
    simp only [Q,mem_insert,mem_singleton] at xy
    obtain ⟨a,_,lt⟩ := props x hx
    rcases xy with e|e|e
    · exact ((mem_erase.mp a).1 e).elim
    · exact e
    · have ly := (props y hy).2.2
      rw [e,show p (p y)=y from F.invol c y] at lt
      exact (lt.asymm ly).elim
  let family := E.image freeQ
  let z' : Free B := ⟨z,map_free B X zS⟩
  apply trim_nine shortLevels _ X z' family sz ((card_image_of_injOn eqQ).trans four) (by decide)
  intro T ht
  obtain ⟨x,hx,rfl⟩ := mem_image.mp ht
  obtain ⟨xr,pxr,lt⟩ := props x hx
  have qsz : (Q x).card=3 := by
    simp [Q,(mem_erase.mp xr).1.symm,(mem_erase.mp pxr).1.symm,lt.ne]
  have size : (freeQ x).card=3 := by rw [←card_map (f:=emb B),back x hx,qsz]
  have ssub : freeQ x⊆X := map_subset_map.mp ((back x hx).symm ▸ inside x hx)
  have zmem : z'∈freeQ x := mem_subtype.mpr (mem_insert_self _ _)
  refine ⟨size,ssub,zmem,(mem_gather _ _ _).mpr ⟨{r},short_root _ _ _ _ _,pull_mem.mpr ⟨size,c,?_⟩⟩⟩
  rw [back x hx]
  intro v hv
  change p v∈{r} ∪ Q x
  simp only [Q,mem_union,mem_insert,mem_singleton] at hv ⊢
  rcases hv with e|e|e|e
  · exact Or.inr (Or.inl (e ▸ rfl))
  · exact Or.inl (e ▸ pz)
  · exact Or.inr (Or.inr (Or.inr (e ▸ rfl)))
  · exact Or.inr (Or.inr (Or.inl (e ▸ F.invol c x)))
end WildSieve
