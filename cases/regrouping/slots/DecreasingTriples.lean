import CutRank
import Mathlib.Order.PiLex
import Mathlib.Logic.Equiv.Fintype

namespace WildSlots
open Finset WildDeletion
private abbrev T := Fin 3

/-- Permutations with no three positions whose destinations are in strictly decreasing order. -/
def avoids {n : Nat} (p : Perm (Fin n)) :=
  ∀ i j k : Fin n,i<j → j<k → p j<p i → ¬p k<p j
instance {n : Nat} (p : Perm (Fin n)) : Decidable (avoids p) :=
  inferInstanceAs (Decidable (∀ i j k : Fin n,i<j → j<k → p j<p i → ¬p k<p j))
def sample (n : Nat) := univ.filter (@avoids n)

private def sign (q : Perm T) : ℤ :=
  if q=1 ∨ (q 0=1 ∧ q 1=2) ∨ (q 0=2 ∧ q 1=0) then 1 else -1

private def weight (q : Perm T) : ℚ := sign q
private theorem balance : ∑ q,weight q=0 := by
  have h : ∑ q,sign q=0 := by decide
  simpa only [weight,Int.cast_sum,Int.cast_zero] using congrArg (fun x : ℤ => (x:ℚ)) h
private theorem cancel (a b : T → Bool) : ∑ q,weight q * mark a b q=0 := by
  have h : ∀ f g : T → Bool,∑ q,sign q * (if fits f g q then 1 else 0 : ℤ)=0 := by decide
  have step (q : Perm T) : ((if fits a b q then 1 else 0 : ℤ) : ℚ)=mark a b q := by
    by_cases yes : fits a b q <;> simp [mark,yes]
  simpa only [Int.cast_sum,Int.cast_mul,step,Int.cast_zero,weight] using congrArg (fun x : ℤ => (x:ℚ)) (h a b)
private theorem first_change : ∀ q : Perm T,q≠1 → ∃ t : T,t<q t ∧ ∀ i<t,q i=i := by decide

private def shuffled {n : Nat} (p : Perm (Fin n)) (e : T ↪ Fin n) (q : Perm T) :=
  (q.viaFintypeEmbedding e).trans p

private theorem at_point {n : Nat} (p : Perm (Fin n)) (e : T ↪ Fin n) (q : Perm T) (i : T) :
    shuffled p e q (e i)=p (e (q i)) := by simp [shuffled]

private theorem outside {n : Nat} (p : Perm (Fin n)) (e : T ↪ Fin n) (q : Perm T)
    {i : Fin n} (off : i∉Set.range e) : shuffled p e q i=p i := by
  simp [shuffled,Equiv.Perm.viaFintypeEmbedding_apply_not_mem_range _ _ off]

private theorem shuffle_one {n : Nat} (p : Perm (Fin n)) (e : T ↪ Fin n) : shuffled p e 1=p := by
  apply Equiv.ext
  intro i
  by_cases hit : i∈Set.range e
  · obtain ⟨j,rfl⟩ := hit
    simp [at_point]
  · exact outside _ _ _ hit

private theorem cut_cancels {n : Nat} (p : Perm (Fin n)) (e : T ↪ Fin n) (a b : Fin n → Bool) :
    ∑ q,weight q * mark a b (shuffled p e q)=0 := by
  by_cases agree : ∀ i,i∉Set.range e → a i=b (p i)
  · have rel (q : Perm T) : fits a b (shuffled p e q) ↔ fits (a ∘ e) (fun i => b (p (e i))) q := by
      refine ⟨fun h i => by simpa [at_point] using h (e i),?_⟩
      intro h i
      by_cases hit : i∈Set.range e
      · obtain ⟨j,rfl⟩ := hit
        simpa [at_point] using h j
      · rw [outside _ _ _ hit]
        exact agree _ hit
    simpa only [mark,rel] using cancel (a ∘ e) (fun i => b (p (e i)))
  · have no (q : Perm T) : ¬fits a b (shuffled p e q) := fun yes =>
      agree (fun i off => by simpa [outside _ _ _ off] using yes i)
    simp [mark,no]

private theorem weighted_cancel {n : Nat} (p : Perm (Fin n)) (e : T ↪ Fin n)
    {H : Type} [Fintype H] (a b : H → Fin n → Bool) (z : H → ℚ) (s : ℚ) :
    ∑ q,weight q * (s+∑ h,z h*mark (a h) (b h) (shuffled p e q))=0 := by
  simp_rw [mul_add,Finset.mul_sum]
  rw [Finset.sum_add_distrib,←Finset.sum_mul,balance,zero_mul,zero_add,Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro h _
  simp_rw [mul_left_comm (weight _) (z h)]
  rw [←Finset.mul_sum,cut_cancels,mul_zero]

private def key {n : Nat} (p : Perm (Fin n)) := toLex (fun i => p i)

private theorem smaller {n : Nat} (p : Perm (Fin n)) (e : T ↪ Fin n) (inc : StrictMono e)
    (dec : StrictAnti (fun i => p (e i))) {q : Perm T} (move : q≠1) :
    key (shuffled p e q)<key p := by
  obtain ⟨t,ht,first⟩ := first_change q move
  refine ⟨e t,?_,?_⟩
  · intro i hi
    by_cases hit : i∈Set.range e
    · obtain ⟨j,rfl⟩ := hit
      change shuffled p e q (e j)=p (e j)
      rw [at_point,first j (inc.lt_iff_lt.mp hi)]
    · exact outside _ _ _ hit
  · change shuffled p e q (e t)<p (e t)
    simpa only [at_point] using dec ht

private theorem has_triple {n : Nat} (p : Perm (Fin n)) (no : ¬avoids p) :
    ∃ e : T ↪ Fin n,StrictMono e ∧ StrictAnti (fun i => p (e i)) := by
  unfold avoids at no
  push_neg at no
  obtain ⟨i,j,k,ij,jk,down,down'⟩ := no
  have ik := lt_trans ij jk
  have last := lt_trans down' down
  let f (x : T) := if x=0 then i else if x=1 then j else k
  have inc : StrictMono f := by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all [f]
  refine ⟨⟨f,inc.injective⟩,inc,?_⟩
  intro x y h
  fin_cases x <;> fin_cases y <;> simp_all [f]

/-- For every number of slots, checking weighted cut indicators on the
321-avoiding permutations determines their values on all permutations. -/
theorem avoids_detects (n : Nat) : Detects (sample n) := by
  classical
  intro H _ a b z s hs
  let F (p : Perm (Fin n)) := s+∑ h,z h*mark (a h) (b h) p
  by_contra! fails
  let bad := univ.filter (fun p => F p≠0)
  obtain ⟨p,hp⟩ := fails
  obtain ⟨q,hq,smallest⟩ := bad.exists_min_image key ⟨p,mem_filter.mpr ⟨mem_univ _,hp⟩⟩
  have nonzero := (mem_filter.mp hq).2
  have no : ¬avoids q := fun h => nonzero (hs q (mem_filter.mpr ⟨mem_univ _,h⟩))
  obtain ⟨e,inc,dec⟩ := has_triple q no
  have vanishes (r : Perm T) (hr : r≠1) : F (shuffled q e r)=0 := by
    by_contra nz
    exact (not_lt_of_ge (smallest _ (mem_filter.mpr ⟨mem_univ _,nz⟩))) (smaller q e inc dec hr)
  have eq : ∑ r,weight r * F (shuffled q e r)=0 := weighted_cancel q e a b z s
  rw [Finset.sum_eq_single 1 (fun r _ hr => by rw [vanishes r hr,mul_zero]) (by simp)] at eq
  exact nonzero (by simpa [weight,sign,shuffle_one] using eq)

/-- A failed common reassignment always has a witness using at most as many
colors as there are 321-avoiding permutations of the movable vertices. -/
theorem avoiding_palette {V C : Type} (n : Nat) (E : C → V → V → Prop)
    (sym : ∀ c {x y},E c x y → E c y x) (u v : Fin n → V) :
    (∃ p : Perm (Fin n),passes E u v (assign p)) ↔
    ∀ S : Finset C,S.card≤(sample n).card → ∃ p : Perm (Fin n),
      ∀ c∈S,Connected (extend (E c) u v (assign p)) :=
  palette_from_sample _ (avoids_detects n) E sym u v

#print axioms avoiding_palette
end WildSlots
