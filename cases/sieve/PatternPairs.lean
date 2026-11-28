import TriplePatterns
import WedgeCount

namespace WildSieve.SixCounts
open Finset
variable {n k : Nat}
local notation "V" => Fin n
local notation "C" => Fin k
local instance (priority := 2000) pairsEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq

local notation "Pattern" => Blocks V
noncomputable abbrev family (F : Factor V C) := patterns F univ

/-- Two compatible patterns with four different triple blocks. -/
def Separate (M J : Pattern) := vertices J⊆(vertices M)ᶜ
/-- Two compatible, distinct patterns sharing one triple. -/
def Wedge (M J : Pattern) := M≠J ∧ Triples (M∪J) ∧ ¬Disjoint M J

noncomputable def wide (F : Factor V C) : Finset (Pattern × Pattern) := by
  classical exact (family F ×ˢ family F).filter (fun p => Separate p.1 p.2)
noncomputable def touching (F : Factor V C) : Finset (Pattern × Pattern) := by
  classical exact (family F ×ˢ family F).filter (fun p => Wedge p.1 p.2)

theorem separate_iff (M J : Pattern) : Separate M J ↔ Disjoint (vertices M) (vertices J) := by
  constructor
  · exact fun h => disjoint_left.mpr (fun _ a b => mem_compl.mp (h b) a)
  · exact fun h x hx => mem_compl.mpr (fun m => disjoint_left.mp h m hx)

theorem wide_tally (F : Factor V C) :
    (wide F).card=100*∑ T∈marks F univ,(marks F Tᶜ).card := by
  classical
  have row (M : Pattern) :
      (∑ J∈family F,if vertices J⊆(vertices M)ᶜ then 1 else 0)=10*(marks F (vertices M)ᶜ).card := by
    rw [←pattern_card,pattern_filter]
    simp
  calc
    _ = ∑ M∈family F,∑ J∈family F,if vertices J⊆(vertices M)ᶜ then 1 else 0 := by
      rw [←sum_product']; simp [wide,Separate]
      congr 1
      ext p; simp
    _ = _ := by
      simp_rw [row]
      rw [←mul_sum,weight_patterns F univ (fun T => (marks F Tᶜ).card),←mul_assoc]
      rfl

private theorem triple_separate {F : Factor V C} {A B : Finset V} (hb : B∈neighbors F A) :
    Disjoint A B := disjoint_left.mpr (fun _ h k => mem_compl.mp ((neigh_mem.mp hb).1 k) h)

private theorem different {A B : Finset V} (s : A.card=3) (dis : Disjoint A B) : A≠B := by
  rintro rfl
  obtain ⟨x,hx⟩ := card_pos.mp (by omega : 0<A.card)
  exact disjoint_left.mp dis hx hx

private theorem wedge_of_neighbors {F : Factor V C} {A B D : Finset V} (a : A.card=3)
    (b : B∈neighbors F A) (d : D∈neighbors F A) (sep : Disjoint B D) :
    Wedge ({A,B} : Pattern) {A,D} := by
  have ab := triple_separate b
  have ad := triple_separate d
  have abn := different a ab
  have adn := different a ad
  have bdn := different (neigh_mem.mp b).2.1 sep
  have only : Triples ({D} : Pattern) := by
    constructor
    · intro Z h; simpa only [mem_singleton.mp h] using (neigh_mem.mp d).2.1
    · intro X x Y y ne
      exact (ne ((mem_singleton.mp x).trans (mem_singleton.mp y).symm)).elim
  have root := (pattern_mem.mp (pair_pattern a b)).1
  have good := root.combine only (show Disjoint (vertices ({A,B} : Pattern)) (vertices {D}) by
    simpa [vertices] using disjoint_union_left.mpr ⟨ad,sep⟩)
  refine ⟨?_,?_,?_⟩
  · intro e
    have h : B∈({A,D} : Pattern) := e ▸ (show B∈({A,B} : Pattern) by simp)
    simp [abn.symm,bdn] at h
  · convert good using 1
    ext X
    simp [or_comm,or_assoc,or_left_comm]
  · exact fun dis => disjoint_left.mp dis (mem_insert_self _ _) (mem_insert_self _ _)

theorem touching_tally (F : Factor V C) : (∑ A∈triples n,(wedgesAt F A).card)≤(touching F).card := by
  classical
  let S := (triples n).sigma (wedgesAt F)
  let pack (p : (A : Finset V) × (Finset V × Finset V)) : Pattern × Pattern :=
    (⟨{p.1,p.2.1},{p.1,p.2.2}⟩)
  have facts {A B D : Finset V} (h : (⟨A,(B,D)⟩ : (A : Finset V) × (Finset V × Finset V))∈S) :
      A.card=3 ∧ B∈neighbors F A ∧ D∈neighbors F A ∧ Disjoint B D := by
    obtain ⟨ha,p⟩ := mem_sigma.mp h
    obtain ⟨p,dis⟩ := mem_filter.mp p
    exact ⟨triple_mem.mp ha,(mem_product.mp p).1,(mem_product.mp p).2,dis⟩
  have send (p) (h : p∈S) : pack p∈touching F := by
    rcases p with ⟨A,B,D⟩
    obtain ⟨a,b,d,sep⟩ := facts h
    exact mem_filter.mpr ⟨mem_product.mpr ⟨pair_pattern a b,pair_pattern a d⟩,wedge_of_neighbors a b d sep⟩
  have split {A B D : Finset V} (h : (⟨A,(B,D)⟩ : (A : Finset V) × (Finset V × Finset V))∈S) :
      ({A,B} : Pattern)∩{A,D}={A} ∧ B≠A ∧ D≠A := by
    obtain ⟨a,b,d,sep⟩ := facts h
    have bd := different (neigh_mem.mp b).2.1 sep
    refine ⟨?_,(different a (triple_separate b)).symm,(different a (triple_separate d)).symm⟩
    ext Z; simp only [mem_inter,mem_insert,mem_singleton]
    constructor
    · rintro ⟨h|h,k|k⟩ <;> first | assumption | exact (bd (h.symm.trans k)).elim
    · intro h; exact ⟨Or.inl h,Or.inl h⟩
  have inj : Set.InjOn pack S := by
    rintro ⟨A,B,D⟩ h ⟨X,Y,Z⟩ k eq
    obtain ⟨e,ba,da⟩ := split h
    obtain ⟨u,yx,zx⟩ := split k
    have center := congrArg (fun p : Pattern × Pattern => p.1∩p.2) eq
    change ({A,B} : Pattern)∩{A,D} = ({X,Y} : Pattern)∩{X,Z} at center
    rw [e,u,singleton_inj] at center
    subst X
    obtain ⟨l,r⟩ := Prod.mk.inj eq
    have left := congrArg (fun P : Pattern => P.erase A) l
    have right := congrArg (fun P : Pattern => P.erase A) r
    simp [ba.symm,yx.symm] at left
    simp [da.symm,zx.symm] at right
    subst Y; subst Z; rfl
  have bound := card_le_card_of_injOn pack send inj
  rw [show S=(triples n).sigma (wedgesAt F) from rfl,card_sigma] at bound
  exact bound

end WildSieve.SixCounts
