import FiberMass
import Mathlib.Algebra.BigOperators.Fin
namespace WildPieces
attribute [local instance 2000] Fintype.decidableForallFintype
set_option maxRecDepth 2000
open Finset
abbrev V := Fin 19
abbrev G := Fin 6
abbrev H := Fin 10

def labels (p : Equiv.Perm V) (x : V) : G := WildCuts.groups19.tag (p x)
def compatible {k : Nat} (a : G → Fin k) (p : Equiv.Perm V) :=
  ∀ x, a (labels p x) = a (labels p ((WildCuts.pairs 19).rep ((WildCuts.pairs 19).tag x)))
instance {k} (a : G → Fin k) (p : Equiv.Perm V) : Decidable (compatible a p) :=
  inferInstanceAs (Decidable (∀ x : V, a (labels p x) =
    a (labels p ((WildCuts.pairs 19).rep ((WildCuts.pairs 19).tag x)))))

theorem unique_words {k} (a : G → Fin k) (p : Equiv.Perm V) :
    (if compatible a p then 1 else 0) =
      ∑ f : H → Fin k, if ∀ x, a (labels p x) = f ((WildCuts.pairs 19).tag x) then 1 else 0 := by
  let truth (f : H → Fin k) := ∀ x, a (labels p x) = f ((WildCuts.pairs 19).tag x)
  let expected := fun i => a (labels p ((WildCuts.pairs 19).rep i))
  have eq (f : H → Fin k) (h : truth f) : f = expected := by
    funext i
    have z := h ((WildCuts.pairs 19).rep i)
    simpa [expected,(WildCuts.pairs 19).section_] using z.symm
  by_cases ok : compatible a p
  · rw [if_pos ok,Finset.sum_eq_single expected]
    · exact (if_pos ok).symm
    · intro f _ ne
      exact if_neg (fun h => ne (eq f h))
    · simp
  · rw [if_neg ok]
    symm
    apply Finset.sum_eq_zero
    intro f _
    apply if_neg
    intro h
    have := eq f h
    subst f
    exact ok h
/-- Count assignments of the colors' nine pairs and one singleton to cells
of prescribed sizes, deducting the selected cell's weight at each step. -/
def ways {k : Nat} : {n : Nat} → (Fin n → Nat) → (Fin k → Nat) → Nat
  | 0, _, need => if ∀ j, need j = 0 then 1 else 0
  | n+1, w, need => ∑ i : Fin k, if w 0 ≤ need i then
      ways (n:=n) (fun t => w t.succ) (Function.update need i (need i-w 0)) else 0

def load {n k : Nat} (w : Fin n → Nat) (f : Fin n → Fin k) (j : Fin k) :=
  ∑ t, if f t = j then w t else 0

private theorem load_cons {n k : Nat} (w : Fin (n+1) → Nat) (v : Fin k) (f : Fin n → Fin k) (j : Fin k) :
    load w (Fin.cons v f) j = (if v=j then w 0 else 0)+load (fun t => w t.succ) f j := by
  unfold load
  rw [Fin.sum_univ_succ]
  simp

theorem ways_correct {n k : Nat} (w : Fin n → Nat) (need : Fin k → Nat) :
    (∑ f : Fin n → Fin k, if ∀ j, load w f j = need j then 1 else 0) = ways w need := by
  induction n generalizing need with
  | zero =>
    simp [load,ways,eq_comm]
  | succ n ih =>
    let e := Fin.consEquiv (fun _ : Fin (n+1) => Fin k)
    rw [← Fintype.sum_equiv e _ _ (fun _ => rfl), Fintype.sum_prod_type]
    change (∑ i : Fin k, ∑ f : Fin n → Fin k, if ∀ j, load w (Fin.cons i f) j = need j then 1 else 0) = _
    unfold ways
    apply Finset.sum_congr rfl
    intro i _
    by_cases enough : w 0 ≤ need i
    · rw [if_pos enough,← ih]
      apply Finset.sum_congr rfl
      intro f _
      congr 1
      apply propext
      simp only [load_cons]
      constructor <;> intro h j <;> by_cases eq : i=j
      · subst j; have := h i; simp at this; simp; omega
      · simpa [eq,Function.update_of_ne (Ne.symm eq)] using h j
      · subst j; have := h i; simp at this; simp; omega
      · simpa [eq,Function.update_of_ne (Ne.symm eq)] using h j
    · rw [if_neg enough]
      apply Finset.sum_eq_zero
      intro f _
      apply if_neg
      intro h
      have := h i
      simp [load_cons] at this
      omega

def form {k} (a : G → Fin k) := fun x : V => a (WildCuts.groups19.tag x)
def pairWeights := bucketSize (WildCuts.pairs 19).tag

private theorem derived_size {k} (f : H → Fin k) (j : Fin k) :
    bucketSize (fun x : V => f ((WildCuts.pairs 19).tag x)) j = load pairWeights f j := by
  have b := Finset.sum_fiberwise_eq_sum_filter (s:=univ) (t:=univ.filter fun h : H => f h=j)
    (WildCuts.pairs 19).tag (fun _ => (1:Nat))
  simpa [load,bucketSize,pairWeights,Finset.sum_filter] using b.symm

def mass {k} (a : G → Fin k) :=
  ways pairWeights (bucketSize (form a)) * ∏ i, (bucketSize (form a) i).factorial

theorem mass_correct {k} (a : G → Fin k) :
    (∑ p : Equiv.Perm V, if compatible a p then 1 else 0) = mass a := by
  simp_rw [unique_words]
  rw [Finset.sum_comm]
  change (∑ f : H → Fin k, ∑ p : Equiv.Perm V, if ∀ x, form a (p x) = f ((WildCuts.pairs 19).tag x) then 1 else 0) = _
  have each (f : H → Fin k) := label_mass (fun x : V => f ((WildCuts.pairs 19).tag x)) (form a)
  trans ∑ f : H → Fin k, if ∀ i, load pairWeights f i = bucketSize (form a) i then ∏ i, (bucketSize (form a) i).factorial else 0
  · apply Finset.sum_congr rfl
    intro f _
    refine (each f).trans ?_
    congr 1
    apply propext
    exact forall_congr' (fun j => Iff.of_eq (congrArg (· = bucketSize (form a) j) (derived_size f j)))
  unfold mass
  rw [← ways_correct,Finset.sum_mul]
  simp only [ite_mul,one_mul,zero_mul]
end WildPieces
