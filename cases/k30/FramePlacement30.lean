import FrameWeights30
import Sampling30

namespace WildSieve.Thirty.Graph
open Finset
local instance (priority := 2000) placementEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq
set_option maxRecDepth 10000

def splitRegion (L A B : Finset V) (v : V) : Fin 4 :=
  if v∈A then 0 else if v∈B then 1 else if v∈L then 2 else 3

structure Placement (L A B : Finset V) (t : Fin 3) : Prop where
  apart : Disjoint A B
  leftA : ∀ x∈A,x∈L ↔ t.val<2
  leftB : ∀ x∈B,x∈L ↔ t.val=0

theorem split_zones (L A B : Finset V) (ab : Disjoint A B) :
    let z := splitRegion L A B
    zone z 0=A ∧ zone z 1=B ∧ zone z 2=L \ (A∪B) ∧ zone z 3=Lᶜ \ (A∪B) := by
  dsimp only
  refine ⟨?_,?_,?_,?_⟩ <;> ext v <;>
    by_cases a : v∈A <;> by_cases b : v∈B <;> by_cases l : v∈L <;>
    simp [zone,splitRegion,a,b,l] <;> exact False.elim (disjoint_left.mp ab a b)

theorem split_selected (L A B : Finset V) (t : Fin 3) (P : Placement L A B t) :
    selected (splitRegion L A B) (leftMask t)=L ∧ selected (splitRegion L A B) hitMask=A∪B := by
  constructor <;> ext v
  · by_cases a : v∈A
    · simpa [selected,splitRegion,leftMask,a] using (P.leftA v a).symm
    · by_cases b : v∈B
      · simpa [selected,splitRegion,leftMask,a,b] using (P.leftB v b).symm
      · by_cases l : v∈L <;> simp [selected,splitRegion,leftMask,a,b,l]
  · by_cases a : v∈A <;> by_cases b : v∈B <;> by_cases l : v∈L <;> simp [selected,splitRegion,hitMask,a,b,l] <;> decide

theorem split_sizes (L A B : Finset V) (t : Fin 3) (P : Placement L A B t)
    (l : L.card=12) (a : A.card=3) (b : B.card=3) (kind : ((A∪B)∩L).card=6-3*t.val) :
    ∀ i,(zone (splitRegion L A B) i).card=zoneSize t i := by
  let z := splitRegion L A B
  obtain ⟨zero,one,two,_⟩ := split_zones L A B P.apart
  have remainder := card_sdiff_add_card_inter L (A∪B)
  rw [inter_comm L,kind,l] at remainder
  have all := occupancy_total univ z
  simp only [occupancy,univ_inter,z,zero,one,a,b,two,card_univ,Fintype.card_fin] at all
  have bound := t.isLt
  have four : ∀ i : Fin 4,i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by decide
  intro j
  rcases four j with rfl|rfl|rfl|rfl <;> simp only [zoneSize,Fin.val_zero,Fin.reduceFinMk,zero,one,two,a,b,leftFree] <;> omega

theorem sealed_triple (D : Deck) (A : Finset V) (size : A.card=3) :
    D∈localSeal univ A ↔ A∈D.val := by
  constructor
  · intro h
    obtain ⟨M,hm⟩ := local_seal_mem.mp h
    have card := M.property.1.card_vertices
    rw [M.property.2,size] at card
    obtain ⟨b,eq⟩ := card_eq_one.mp (show M.val.card=1 by omega)
    have ve := M.property.2
    rw [eq,vertices_singleton] at ve
    exact ve ▸ hm (eq ▸ mem_singleton_self b)
  · intro h
    exact local_seal_mem.mpr ⟨⟨{A},singleton_triple size,vertices_singleton _⟩,singleton_subset_iff.mpr h⟩

theorem split_decks (L A B : Finset V) (t : Fin 3) (P : Placement L A B t)
    (a : A.card=3) (b : B.card=3) (D : Deck) :
    D∈Regions.decks (splitRegion L A B) ↔ D∈localSeal univ L ∧ A∈D.val ∧ B∈D.val := by
  let z := splitRegion L A B
  obtain ⟨zero,one,_,_⟩ := split_zones L A B P.apart
  constructor
  · intro h
    have same := (Regions.decks_constant _ _).mp h
    have regions := Regions.decks_mem.mp h
    have s0 := regions 0
    have s1 := regions 1
    change D∈localSeal univ (zone z 0) at s0
    change D∈localSeal univ (zone z 1) at s1
    rw [show zone z 0=A from zero] at s0
    rw [show zone z 1=B from one] at s1
    refine ⟨(seal_whole (subset_univ _) D).mpr ?_,(sealed_triple D A a).mp s0,(sealed_triple D B b).mp s1⟩
    intro hblock hb v hv vl w hw
    rw [←(split_selected L A B t P).1] at vl ⊢
    exact mem_filter.mpr ⟨mem_univ _,same hblock hb v hv w hw ▸ (mem_filter.mp vl).2⟩
  · rintro ⟨sealed,ha,hb⟩
    apply (Regions.decks_constant _ _).mpr
    intro block h v hv w hw
    have same (S : Finset V) (closed : D∈localSeal univ S) : v∈S ↔ w∈S := by
      have law := (seal_whole (subset_univ _) D).mp closed
      exact ⟨fun vs => law block h v hv vs hw,fun ws => law block h w hw ws hv⟩
    simp only [splitRegion,same A ((sealed_triple D A a).mpr ha),same B ((sealed_triple D B b).mpr hb),same L sealed]

end WildSieve.Thirty.Graph
