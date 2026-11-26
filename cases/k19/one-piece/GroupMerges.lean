import BinMass
namespace WildPieces
open Finset WildCuts
abbrev Tags := G → G

def merge (t : Tags) (e : G × G) : Tags := fun i => if t i = t e.2 then t e.1 else t i
def finish (t : Tags) (es : List (G × G)) := es.foldl merge t
def links (p : Equiv.Perm V) := (List.finRange 19).map fun x =>
  (labels p x,labels p ((pairs 19).rep ((pairs 19).tag x)))
def components (p : Equiv.Perm V) := finish id (links p)
def coarse {k} (t : Tags) (a : G → Fin k) := ∀ i j, t i = t j → a i = a j
instance {k} (t : Tags) (a : G → Fin k) : Decidable (coarse t a) :=
  inferInstanceAs (Decidable (∀ i j : G, t i = t j → a i = a j))

private theorem old_eq (t : Tags) (e : G × G) {i j} (h : t i = t j) : merge t e i = merge t e j := by
  simp [merge,h]
private theorem tied (t : Tags) (e : G × G) : merge t e e.1 = merge t e e.2 := by simp [merge]

theorem merge_congr {Z : Type} (R : Z → Z → Prop) (rr : Equivalence R) (f : G → Z)
    (t : Tags) (e : G × G) (h : ∀ i j, t i = t j → R (f i) (f j))
    (edge : R (f e.1) (f e.2)) : ∀ i j, merge t e i = merge t e j → R (f i) (f j) := by
  intro i j eq
  by_cases ai : t i = t e.2 <;> by_cases aj : t j = t e.2 <;> simp only [merge,ai,aj,if_true,if_false] at eq
  · exact h _ _ (ai.trans aj.symm)
  · exact rr.trans (h _ _ ai) (rr.trans (rr.symm edge) (h _ _ eq))
  · exact rr.trans (h _ _ eq) (rr.trans edge (h _ _ aj.symm))
  · exact h _ _ eq

theorem finish_congr {Z : Type} (R : Z → Z → Prop) (rr : Equivalence R) (f : G → Z)
    (t : Tags) (es : List (G × G)) (h : ∀ i j, t i = t j → R (f i) (f j))
    (edges : ∀ e ∈ es, R (f e.1) (f e.2)) : ∀ i j, finish t es i = finish t es j → R (f i) (f j) := by
  induction es generalizing t with
  | nil => exact h
  | cons e ls ih =>
    exact ih _ (merge_congr _ rr f _ e h (edges e (by simp))) (fun x hx => edges _ (by simp [hx]))

theorem coarse_merge {k} (t : Tags) (e : G × G) (a : G → Fin k) :
    coarse (merge t e) a ↔ coarse t a ∧ a e.1 = a e.2 := by
  constructor
  · intro h
    exact ⟨fun i j eq => h i j (old_eq t e eq),h _ _ (tied _ _)⟩
  · rintro ⟨h,he⟩
    exact merge_congr Eq ⟨Eq.refl,Eq.symm,Eq.trans⟩ _ _ _ h he

theorem coarse_finish {k} (t : Tags) (es : List (G × G)) (a : G → Fin k) :
    coarse (finish t es) a ↔ coarse t a ∧ ∀ e ∈ es, a e.1 = a e.2 := by
  induction es generalizing t with
  | nil => simp [finish]
  | cons e ls ih =>
    change coarse (finish (merge t e) ls) a ↔ _
    rw [ih,coarse_merge]
    simp [and_assoc]

theorem coarse_components {k} (p : Equiv.Perm V) (a : G → Fin k) :
    coarse (components p) a ↔ compatible a p := by
  rw [components,coarse_finish]
  have base : coarse id a := fun i j eq => congrArg a eq
  simp [base,links,compatible]

def deficit (t : Tags) := (univ.image t).card-1
end WildPieces
