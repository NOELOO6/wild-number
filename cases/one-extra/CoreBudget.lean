import TwoGroupCore
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

namespace WildCuts.OneExtra
open Finset WildExact WildDeletion

/-- Name a bipartition by its side away from a fixed root. -/
def choices {V : Type} [DecidableEq V] (R : Finset V) (r : V) :=
  (R.erase r).powerset.filter (fun A => 3≤A.card ∧ A.card+3≤R.card)

def splitCount (s : Nat) := ∑ j∈range ((s-1)+1),
  (if 3≤j ∧ j+3≤s then (s-1).choose j else 0)

theorem choices_count {V : Type} [DecidableEq V] (R : Finset V) {r : V} (hr : r∈R) :
    (choices R r).card=splitCount R.card := by
  let f (j : Nat) : Nat := if 3≤j ∧ j+3≤R.card then 1 else 0
  have count : (choices R r).card=∑ A∈(R.erase r).powerset,f A.card := by
    simp [choices,f,sum_boole]
  rw [count,sum_powerset]
  simp only [sum_powersetCard,card_erase_of_mem hr,nsmul_eq_mul]
  apply sum_congr rfl
  intro j _
  simp only [f]
  split <;> simp_all

theorem small_counts : splitCount 6=10 ∧ splitCount 7=35 ∧ splitCount 8=91 := by decide

theorem side_info {n : Nat} {R A : Finset (Fin n)} {r} (ha : A∈choices R r) :
    A⊆R ∧ r∉A ∧ A.Nonempty := by
  obtain ⟨sub,sz,_⟩ := mem_filter.mp ha
  have ss := mem_powerset.mp sub
  exact ⟨ss.trans (erase_subset _ _),fun h => not_mem_erase _ _ (ss h),card_pos.mp (by omega)⟩

def crossing {n k : Nat} (g : Coloring n k) (w : Lines n) (R : Finset (Fin n)) (c : Fin k)
    (A : Finset (Fin n)) := ∃ x∈A,∃ y∈R\A,Walk (Joined g w c) x y

noncomputable def blocked {n k : Nat} (g : Coloring n k) (w : Lines n) (R : Finset (Fin n))
    (r : Fin n) (c : Fin k) : Finset (Finset (Fin n)) := by
  classical
  exact (choices R r).filter (fun A => ¬crossing g w R c A)

theorem affordable {n k limit : Nat} (pos : 0<k) (g : Coloring n k) (w : Lines n)
    (R : Finset (Fin n)) (r : Fin n) (hr : r∈R) (legal : Legal w) (reach : MeetsCore g w R)
    (loss : Fin k → Nat) (bound : ∀ c,(blocked g w R r c).card≤loss c)
    (count : (∑ c,loss c)<splitCount R.card) (budget : w.card+(R.card-2)≤limit) : Upper g limit := by
  classical
  have lost := (card_biUnion_le (s:=univ) (t:=blocked g w R r)).trans (sum_le_sum (fun c _ => bound c))
  obtain ⟨A,ha,free⟩ := exists_mem_not_mem_of_card_lt_card (s:=univ.biUnion (blocked g w R r)) (t:=choices R r)
    (by rw [choices_count R hr];exact lost.trans_lt count)
  have sub := (side_info ha).1
  apply upper_if_two pos g w R A (R\A) legal reach (union_sdiff_of_subset sub) disjoint_sdiff _ budget
  intro c
  by_contra no
  exact free (mem_biUnion.mpr ⟨c,mem_univ _,mem_filter.mpr ⟨ha,no⟩⟩)

/-- If one color meets the core in at most d+1 connected pieces, it can
block at most 2^d-1 of the two-way splits. A connected color costs zero. -/
theorem piece_budget {n k limit : Nat} (pos : 0<k) (g : Coloring n k) (w : Lines n)
    (R : Finset (Fin n)) (r : Fin n) (hr : r∈R) (legal : Legal w) (reach : MeetsCore g w R)
    (d : Fin k → Nat) (rep : (c : Fin k) → Fin (d c) → Fin n) (members : ∀ c j,rep c j∈R)
    (routes : ∀ c x,x∈R → Walk (Joined g w c) x r ∨ ∃ j,Walk (Joined g w c) x (rep c j))
    (count : (∑ c,(2^(d c)-1))<splitCount R.card)
    (budget : w.card+(R.card-2)≤limit) : Upper g limit := by
  classical
  let bad := blocked g w R r
  apply affordable pos g w R r hr legal reach (fun c => 2^(d c)-1) _ count budget
  intro c
  change (bad c).card≤2^(d c)-1
  let code (A : Finset (Fin n)) := univ.filter (fun j : Fin (d c) => rep c j∈A)
  let T := (univ : Finset (Fin (d c))).powerset.erase ∅
  have closed {A} (ha : A∈bad c) {x y} (hx : x∈R) (hy : y∈R) (walk : Walk (Joined g w c) x y) :
      x∈A ↔ y∈A := by
    have no := (mem_filter.mp ha).2
    refine ⟨fun a => by_contra (fun ny => no ⟨x,a,y,mem_sdiff.mpr ⟨hy,ny⟩,walk⟩),
      fun b => by_contra (fun nx => no ⟨y,b,x,mem_sdiff.mpr ⟨hx,nx⟩,backwards (joined_symm g) walk⟩)⟩
  have non {A} (ha : A∈bad c) : (code A).Nonempty := by
    obtain ⟨sub,out,x,hx⟩ := side_info (mem_filter.mp ha).1
    rcases routes c x (sub hx) with path|⟨j,path⟩
    · exact (out ((closed ha (sub hx) hr path).mp hx)).elim
    · exact ⟨j,mem_filter.mpr ⟨mem_univ _,(closed ha (sub hx) (members c j) path).mp hx⟩⟩
  have cap := card_le_card_of_injOn (s:=bad c) (t:=T) code
    (fun A ha => mem_erase.mpr ⟨(non ha).ne_empty,mem_powerset.mpr (subset_univ _)⟩) (by
      intro A ha B hb eq
      change code A=code B at eq
      obtain ⟨sa,ra,_⟩ := side_info (mem_filter.mp ha).1
      obtain ⟨sb,rb,_⟩ := side_info (mem_filter.mp hb).1
      ext x
      by_cases hx : x∈R
      · rcases routes c x hx with path|⟨j,path⟩
        · rw [closed ha hx hr path,closed hb hx hr path]
          exact iff_of_false ra rb
        · rw [closed ha hx (members c j) path,closed hb hx (members c j) path]
          simpa only [code,mem_filter,mem_univ,true_and] using
            (show j∈code A ↔ j∈code B by rw [eq])
      · exact iff_of_false (fun h => hx (sa h)) (fun h => hx (sb h)))
  simpa [T,card_erase_of_mem (show (∅ : Finset (Fin (d c)))∈univ.powerset by simp)] using cap

#print axioms piece_budget
end WildCuts.OneExtra
