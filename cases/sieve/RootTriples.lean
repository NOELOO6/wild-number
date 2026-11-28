import SplitLayout

namespace WildSieve
open Finset
variable {A C : Type} [LinearOrder A] [Fintype A] [Fintype C]

/-- Ordinary triples which the distinguished root completes to a closed
four-set in at least one color. Repetitions across colors count once. -/
noncomputable def rootTriples (F : Factor A C) (r : A) := sides F {r} {r}ᶜ 3

/-- Maximum number of these triples through one ordinary point. -/
def VertexCap (F : Factor A C) (r : A) (k : Nat) : Prop :=
  ∀ z,z≠r → ((rootTriples F r).filter (fun X => z∈X)).card≤k

/-- Maximum number of these triples through two distinct ordinary points. -/
def PairCap (F : Factor A C) (r : A) (d : Nat) : Prop :=
  ∀ z y,z≠r → y≠r → y≠z → ((rootTriples F r).filter (fun X => z∈X ∧ y∈X)).card≤d

private theorem from_ordinary (F : Factor A C) (B : Finset A) (r : A) (hr : r∈B)
    (X : Finset (Free B)) (hx : X∈ordinaryScopes F B r 1) :
    X.card=3 ∧ X.map (emb B)∈rootTriples F r := by
  obtain ⟨D,mem,xd⟩ := (mem_gather _ _ X).mp hx
  obtain ⟨size,c,cl⟩ := pull_mem.mp xd
  have sz : X.card=3 := size
  refine ⟨sz,?_⟩
  have sub : X.map (emb B)⊆{r}ᶜ := by
    intro x h
    exact mem_compl.mpr (fun v => (mem_compl.mp (map_free _ _ h)) ((mem_singleton.mp v) ▸ hr))
  rcases (show D=∅ ∨ D={r} by simpa [ordinaryD] using mem) with rfl|rfl
  · rw [empty_union] at cl
    have even := closed_size (F.invol c) (F.moving c) cl
    rw [card_map,sz] at even
    omega
  · exact side_mem.mpr ⟨c,candidate_mem.mpr ⟨sub,by simpa using sz,cl⟩⟩

theorem root_vertex_bound (F : Factor A C) (B : Finset A) (r : A) (hr : r∈B) (k : Nat)
    (cap : VertexCap F r k) (U : Finset (Free B)) (z : Free B) :
    (active (ordinaryScopes F B r 1) U z).card≤k := by
  apply le_trans _ (cap z.val (fun e => (mem_compl.mp z.property) (e ▸ hr)))
  apply card_le_card_of_injOn (Finset.map (emb B)) _ (Finset.map_injective _).injOn
  intro X hx
  obtain ⟨h,_,zx⟩ := mem_filter.mp hx
  exact mem_filter.mpr ⟨(from_ordinary F B r hr X h).2,mem_map.mpr ⟨z,zx,rfl⟩⟩

theorem root_pair_bound (F : Factor A C) (B : Finset A) (r : A) (hr : r∈B) (d : Nat)
    (cap : PairCap F r d) (U : Finset (Free B)) (z : Free B) (zu : z∈U) :
    (active (ordinaryScopes F B r 1) U z).card≤d*(U.card-1)/2 := by
  classical
  let H := active (ordinaryScopes F B r 1) U z
  let Y := U.erase z
  have two (X : Finset (Free B)) (hx : X∈H) : (Y.filter (·∈X)).card=2 := by
    obtain ⟨h,xu,zx⟩ := mem_filter.mp hx
    have eq : Y.filter (·∈X)=X.erase z := by
      ext v
      simp only [Y,mem_filter,mem_erase]
      exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,xu h.2⟩,h.2⟩⟩
    rw [eq,card_erase_of_mem zx,(from_ordinary F B r hr X h).1]
  have per (y : Free B) (hy : y∈Y) : (H.filter (fun X => y∈X)).card≤d := by
    apply le_trans _ (cap z y (fun e => (mem_compl.mp z.property) (e ▸ hr))
      (fun e => (mem_compl.mp y.property) (e ▸ hr)) (fun e => (mem_erase.mp hy).1 (Subtype.ext e)))
    apply card_le_card_of_injOn (Finset.map (emb B)) _ (Finset.map_injective _).injOn
    intro X hx
    obtain ⟨h,yx⟩ := mem_filter.mp hx
    obtain ⟨h,_,zx⟩ := mem_filter.mp h
    exact mem_filter.mpr ⟨(from_ordinary F B r hr X h).2,mem_map.mpr ⟨z,zx,rfl⟩,mem_map.mpr ⟨y,yx,rfl⟩⟩
  have bound : H.card*2≤d*(U.card-1) := calc
    H.card*2 = ∑ X∈H,(Y.filter (·∈X)).card := by
      rw [sum_congr rfl two];simp
    _ = ∑ y∈Y,(H.filter (fun X => y∈X)).card := by
      simp only [Finset.card_filter]
      rw [sum_comm]
    _ ≤ ∑ _∈Y,d := sum_le_sum per
    _ = d*(U.card-1) := by simp [Y,card_erase_of_mem zu,Nat.mul_comm]
  change H.card≤_
  omega

end WildSieve
