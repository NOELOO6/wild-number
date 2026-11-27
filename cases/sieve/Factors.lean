import MatchingCuts
import MatchingModel
import Mathlib.Data.Fintype.BigOperators
namespace WildSieve
open Finset
variable {A C : Type} [LinearOrder A]

/-- Edge-disjoint perfect matchings covering every edge of the complete graph. -/
structure Factor (A C : Type) where
  f : C → A → A
  invol : ∀ c, Function.Involutive (f c)
  moving : ∀ c x, x ≠ f c x
  unique : ∀ x, Function.Injective (fun c => f c x)
  edge : ∀ x y, x ≠ y → ∃ c, f c x=y

noncomputable def coloringFactor {n : Nat} (g : WildExact.Coloring (n+1) n) :
    Factor (Fin (n+1)) (Fin n) where
  f := WildExact.mate g
  invol := WildExact.mate_involutive g
  moving := fun c x => (WildExact.mate_spec g c x).1
  unique := by
    intro x c d eq
    have a := (WildExact.mate_spec g c x).2
    have b := (WildExact.mate_spec g d x).2
    exact a.symm.trans ((congrArg (g.paint x) eq).trans b)
  edge := by
    intro x y xy
    refine ⟨g.paint x y,?_⟩
    obtain ⟨ne,col⟩ := WildExact.mate_spec g (g.paint x y) x
    exact g.proper _ _ _ ne xy col

def Inside (F : Factor A C) (c : C) (B : Finset A) := (lowerEnds (F.f c) B).card

def Rainbow (F : Factor A C) (B : Finset A) := ∀ c, Inside F c B ≤ 1

theorem inside_mono (F : Factor A C) (c : C) {B U : Finset A} (sub : B⊆U) :
    Inside F c B ≤ Inside F c U := card_le_card (lower_mono _ sub)

private theorem unique_on_pair (F : Factor A C) {q : Finset A} (size : q.card=2) :
    ∃! c, Closed (F.f c) q := by
  obtain ⟨a,b,ab,rfl⟩ := card_eq_two.mp size
  obtain ⟨c,hc⟩ := F.edge a b ab
  have bc : F.f c b=a := hc ▸ F.invol c a
  refine ⟨c,?_,?_⟩
  · intro x hx
    simp only [mem_insert,mem_singleton] at hx ⊢
    rcases hx with rfl|rfl
    · exact Or.inr hc
    · exact Or.inl bc
  · intro d hd
    apply F.unique a
    have mem := hd a (mem_insert_self _ _)
    simp only [mem_insert,mem_singleton] at mem
    exact (mem.resolve_left (F.moving d a).symm).trans hc.symm

/-- Count the internal ordinary edges of a point set once, by color. -/
theorem sum_inside [Fintype C] (F : Factor A C) (B : Finset A) :
    ∑ c, Inside F c B = B.card.choose 2 := by
  classical
  let P := ↥(B.powersetCard 2)
  let col (p : P) := (unique_on_pair F (mem_powersetCard.mp p.property).2).choose
  have spec (p : P) : Closed (F.f (col p)) p.val :=
    (unique_on_pair F (mem_powersetCard.mp p.property).2).choose_spec.1
  have one (c : C) : Inside F c B = Fintype.card {p : P // col p = c} := by
    let send (a : ↥(lowerEnds (F.f c) B)) : P :=
      ⟨{a.val,F.f c a.val},mem_powersetCard.mpr
        ⟨insert_subset (mem_filter.mp a.property).1 (singleton_subset_iff.mpr (mem_filter.mp a.property).2.2),
        by simp [F.moving c a.val]⟩⟩
    have fits (a) : col (send a)=c := by
      apply F.unique a.val
      have h := spec (send a) a.val (mem_insert_self _ _)
      change F.f (col (send a)) a.val ∈ {a.val,F.f c a.val} at h
      simpa [(F.moving _ _).symm] using h
    let cert (a) : {p : P // col p=c} := ⟨send a,fits a⟩
    have onto : Function.Surjective cert := by
      rintro ⟨p,hp⟩
      obtain ⟨a,b,ab,pair⟩ := card_eq_two.mp (mem_powersetCard.mp p.property).2
      have cl : Closed (F.f c) p.val := hp ▸ spec p
      have obtainLower (x y : A) (lt : x<y) (eq : p.val={x,y}) : ∃ z,cert z=⟨p,hp⟩ := by
        have fa := cl x (by rw [eq]; simp)
        rw [eq] at fa
        have xy : F.f c x=y := (mem_insert.mp fa).resolve_left (F.moving c x).symm |> mem_singleton.mp
        have sub := (mem_powersetCard.mp p.property).1
        have low : x ∈ lowerEnds (F.f c) B := mem_filter.mpr
          ⟨sub (by rw [eq]; simp),by rwa [xy],sub (by rw [eq,xy]; simp)⟩
        refine ⟨⟨x,low⟩,Subtype.ext (Subtype.ext ?_)⟩
        change {x,F.f c x} = p.val
        rw [xy,eq]
      rcases lt_or_gt_of_ne ab with h|h
      · exact obtainLower a b h pair
      · exact obtainLower b a h (by rw [pair,Finset.pair_comm])
    have inj : Function.Injective cert := by
      intro a b eq
      have e : ({a.val,F.f c a.val} : Finset A)={b.val,F.f c b.val} :=
        congrArg (fun p : {p : P // col p=c} => p.val.val) eq
      have h : a.val ∈ ({b.val,F.f c b.val} : Finset A) := e ▸ mem_insert_self _ _
      rcases (by simpa only [mem_insert,mem_singleton] using h : a.val=b.val ∨ a.val=F.f c b.val) with same|same
      · exact Subtype.ext same
      · have lt := (mem_filter.mp a.property).2.1
        rw [same,F.invol c b.val] at lt
        exact False.elim ((mem_filter.mp b.property).2.1.asymm lt)
    have cnt := Fintype.card_congr (Equiv.ofBijective cert ⟨inj,onto⟩)
    simpa only [Fintype.card_coe,Inside] using cnt
  calc
    _ = ∑ c, Fintype.card {p : P // col p=c} := sum_congr rfl (fun c _ => one c)
    _ = Fintype.card P := by rw [← Fintype.card_sigma]; exact Fintype.card_congr (Equiv.sigmaFiberEquiv col)
    _ = _ := by simp [P]

theorem color_count [Fintype C] (F : Factor A C) {B : Finset A} (rain : Rainbow F B) :
    (univ.filter (fun c => 0 < Inside F c B)).card=B.card.choose 2 := by
  rw [← sum_inside F,card_filter]
  apply sum_congr rfl
  intro c _
  have := rain c
  split <;> omega

end WildSieve
