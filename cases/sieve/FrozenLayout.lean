import SizeBounds
import DegreeChord

namespace WildSieve
open Finset

def gather {α β : Type} [DecidableEq β] (f : α → Finset β) : List α → Finset β
  | [] => ∅
  | a::rest => f a ∪ gather f rest

theorem mem_gather {α β : Type} [DecidableEq β] (f : α → Finset β) (l : List α) (x : β) :
    x ∈ gather f l ↔ ∃ a ∈ l, x ∈ f a := by
  induction l with
  | nil => simp [gather]
  | cons a l ih => simp [gather,ih]

theorem bound_gather {α β : Type} [DecidableEq β] (f : α → Finset β) (l : List α) (q : α → Nat)
    (h : ∀ a ∈ l,(f a).card ≤ q a) : (gather f l).card ≤ (l.map q).sum := by
  induction l with
  | nil => simp [gather]
  | cons a l ih =>
    exact (card_union_le _ _).trans (Nat.add_le_add (h a (by simp))
      (ih (fun x hx => h x (by simp [hx]))))

def choices {A : Type} [DecidableEq A] (B : Finset A) (root : A) (f t j : Nat) :=
  [∅,{root}] ++ if 0<f ∧ 2*j<t then [B.erase root,B] else []

def widths (f t j : Nat) := [0,1] ++ if 0<f ∧ 2*j<t then [f,f+1] else []

def degBound (n f t u j : Nat) := ((widths f t j).map
  (fun d => improvedDegree n (3*t) (f+1) d (3*j) u)).sum

def countBound (n f t j : Nat) := ((widths f t j).map
  (fun d => totalFor n (3*t) (f+1) d (3*j) (3*t))).sum

def shortLevels : Finset Nat := {1,2}
def longLevels (t : Nat) := (range (t/2+1)).filter fun j => 3≤j

def Cert (n f t : Nat) (h : Nat → ℚ) :=
  (∀ u ≤ 3*t,0<h u) ∧ (∀ u,0<u → u≤3*t →
    ∑ j ∈ shortLevels,(degBound n f t u j : ℚ)*(sealWeight t j*h (u-3*j)) ≤ h (u-1)-h u) ∧
  (∑ j ∈ longLevels t,(countBound n f t j : ℚ)*(sealWeight t j*h (3*t-3*j))) < h (3*t)

variable {A C : Type} [LinearOrder A] [Fintype A] [Fintype C]

abbrev Free (B : Finset A) := ↥(Bᶜ : Finset A)
def emb (B : Finset A) : Free B ↪ A := ⟨Subtype.val,Subtype.val_injective⟩

theorem map_free (B : Finset A) (U : Finset (Free B)) : U.map (emb B) ⊆ Bᶜ := by
  intro x hx
  obtain ⟨a,_,rfl⟩ := mem_map.mp hx
  exact a.property

noncomputable def pullSides (F : Factor A C) (B D : Finset A) (s : Nat) : Finset (Finset (Free B)) := by
  classical
  exact (univ.powersetCard s).filter (fun X => ∃ c,Closed (F.f c) (D ∪ X.map (emb B)))

theorem pull_mem {F : Factor A C} {B D : Finset A} {s : Nat} {X : Finset (Free B)} :
    X ∈ pullSides F B D s ↔ X.card=s ∧ ∃ c,Closed (F.f c) (D ∪ X.map (emb B)) := by
  classical
  simp only [pullSides,mem_filter,mem_powersetCard,subset_univ,true_and]

omit [Fintype A] in
theorem choices_sub (B : Finset A) (root : A) (hr : root∈B) (f t j) :
    ∀ D ∈ choices B root f t j,D⊆B := by
  classical
  intro D hd
  by_cases eq : 0<f ∧ 2*j<t <;> simp [choices,eq] at hd
  · rcases hd with rfl|rfl|rfl|rfl
    · exact empty_subset _
    · exact singleton_subset_iff.mpr hr
    · exact erase_subset _ _
    · exact Subset.rfl
  · rcases hd with rfl|rfl
    · exact empty_subset _
    · exact singleton_subset_iff.mpr hr

omit [Fintype A] in
theorem width_eq (B : Finset A) (root : A) (hr : root∈B) (f t j) (sz : B.card=f+1) :
    (choices B root f t j).map Finset.card=widths f t j := by
  by_cases eq : 0<f ∧ 2*j<t <;> simp [choices,widths,eq,card_erase_of_mem hr,sz]

theorem pull_total (F : Factor A C) (B D : Finset A) (s : Nat)
    (rain : Rainbow F B) (db : D⊆B) : (pullSides F B D s).card ≤
    totalFor (Fintype.card C) Bᶜ.card B.card D.card s Bᶜ.card := by
  apply le_trans _ (sides_total F B D Bᶜ s rain db Subset.rfl)
  apply card_le_card_of_injOn (Finset.map (emb B)) _ (Finset.map_injective _).injOn
  intro X hx
  obtain ⟨sz,c,cl⟩ := pull_mem.mp hx
  exact side_mem.mpr ⟨c,candidate_mem.mpr ⟨map_free _ _,by simpa using sz,cl⟩⟩

theorem pull_degree (F : Factor A C) (B D : Finset A) (s : Nat) (U : Finset (Free B))
    (z : Free B) (hz : z∈U) (rain : Rainbow F B) (db : D⊆B) :
    (active (pullSides F B D s) U z).card ≤ improvedDegree (Fintype.card C) Bᶜ.card B.card D.card s U.card := by
  have mem : (emb B) z∈U.map (emb B) := mem_map.mpr ⟨z,hz,rfl⟩
  have b := sides_local_improved F B D (U.map (emb B)) s _ mem rain db (map_free _ _)
  rw [card_map] at b
  apply le_trans _ b
  apply card_le_card_of_injOn (Finset.map (emb B)) _ (Finset.map_injective _).injOn
  intro X hx
  obtain ⟨xm,xu,zx⟩ := mem_filter.mp hx
  obtain ⟨sz,c,cl⟩ := pull_mem.mp xm
  exact mem_filter.mpr ⟨side_mem.mpr ⟨c,candidate_mem.mpr
    ⟨map_subset_map.mpr xu,by simpa using sz,cl⟩⟩,mem_map.mpr ⟨z,zx,rfl⟩⟩

noncomputable def badScopes (F : Factor A C) (B : Finset A) (root : A) (f t j : Nat) :=
  gather (fun D => pullSides F B D (3*j)) (choices B root f t j)

theorem bad_scope_degree (F : Factor A C) (B : Finset A) (root : A) (f t : Nat)
    (hr : root∈B) (bs : B.card=f+1) (ws : Bᶜ.card=3*t) (rain : Rainbow F B)
    (U : Finset (Free B)) (z : Free B) (zu : z∈U) (j : Nat) :
    (active (badScopes F B root f t j) U z).card ≤ degBound (Fintype.card C) f t U.card j := by
  let L := choices B root f t j
  let funD (D) := active (pullSides F B D (3*j)) U z
  have sub : active (badScopes F B root f t j) U z ⊆ gather funD L := by
    intro X hx
    obtain ⟨xb,xu⟩ := mem_filter.mp hx
    obtain ⟨D,dl,xd⟩ := (mem_gather _ _ X).mp xb
    exact (mem_gather _ _ _).mpr ⟨D,dl,mem_filter.mpr ⟨xd,xu⟩⟩
  have b := bound_gather funD L (fun D => improvedDegree (Fintype.card C) Bᶜ.card B.card D.card (3*j) U.card)
    (fun D hd => pull_degree F B D _ U z zu rain (choices_sub B root hr f t j D hd))
  apply (card_le_card sub).trans
  unfold degBound
  rw [← width_eq B root hr f t j bs,List.map_map]
  simpa [L,ws,bs,Function.comp_def] using b

theorem bad_scope_count (F : Factor A C) (B : Finset A) (root : A) (f t : Nat)
    (hr : root∈B) (bs : B.card=f+1) (ws : Bᶜ.card=3*t) (rain : Rainbow F B) (j : Nat) :
    (badScopes F B root f t j).card ≤ countBound (Fintype.card C) f t j := by
  have b := bound_gather (fun D => pullSides F B D (3*j)) (choices B root f t j)
    (fun D => totalFor (Fintype.card C) Bᶜ.card B.card D.card (3*j) Bᶜ.card)
    (fun D hd => pull_total F B D _ rain (choices_sub B root hr f t j D hd))
  unfold countBound
  rw [← width_eq B root hr f t j bs,List.map_map]
  simpa [badScopes,ws,bs,Function.comp_def] using b

/-- A passing numerical certificate supplies a layout for every factorization
with the indicated rainbow frozen set. -/
theorem frozen_layout (F : Factor A C) (B : Finset A) (root : A) (f t : Nat)
    (hr : root∈B) (bs : B.card=f+1) (ws : Bᶜ.card=3*t) (rain : Rainbow F B)
    (h : Nat → ℚ) (cert : Cert (Fintype.card C) f t h) :
    ∃ L : Layout (univ : Finset (Free B)), ∀ j ∈ shortLevels ∪ longLevels t, ∀ X ∈ badScopes F B root f t j,
      L ∉ sealEvent X := by
  classical
  let bad := badScopes F B root f t
  refine partition_from_counts t ((Fintype.card_coe Bᶜ).trans ws) shortLevels (longLevels t) bad ?_ ?_
    (degBound (Fintype.card C) f t) (countBound (Fintype.card C) f t) ?_ ?_ h cert.1 cert.2.1 cert.2.2
  · intro j _ X hx
    obtain ⟨D,_,hx⟩ := (mem_gather _ _ X).mp hx
    exact (pull_mem.mp hx).1
  · intro j hj
    simp [shortLevels] at hj
    omega
  · exact fun U z zu j _ => bad_scope_degree F B root f t hr bs ws rain U z zu j
  · exact fun j _ => bad_scope_count F B root f t hr bs ws rain j
end WildSieve
