import RootContractionParity
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin

namespace WildExact.RootContraction.ThreeCuts
open Finset WildDeletion
variable {V : Type} [Fintype V] [DecidableEq V]

def bit (u : Fin 8) (i : Fin 3) : Bool := u.val.testBit i.val

def encode (f : Fin 3 → Bool) : Fin 8 :=
  ⟨(if f 0 then 1 else 0)+(if f 1 then 2 else 0)+(if f 2 then 4 else 0),
   by split <;> split <;> split <;> decide⟩

private theorem encode_bit : ∀ (f : Fin 3 → Bool) (i : Fin 3), bit (encode f) i=f i := by decide

abbrev ball (p b : Fin 8) := ∀ i j : Fin 3,bit p i≠bit b i → bit p j≠bit b j → i=j
abbrev evenWeight (p : Fin 8) := (univ.filter (fun i : Fin 3 => bit p i)).card%2=0

private abbrev cubeRule (P : Finset (Fin 8)) :=
  0∉P ∨ (∃ i : Fin 3,∀ p∈P,bit p i = false) ∨
  (∃ p∈P,∃ q∈P,∀ i,bit p i≠bit q i) ∨
  (∃ b : Fin 8,∀ p∈P,ball p b) ∨ (∀ p∈P,evenWeight p)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem cube : ∀ P : Finset (Fin 8),cubeRule P := by decide

def signature (S : Fin 3 → Finset V) (x : V) := encode (fun i => decide (x∈S i))

omit [Fintype V] in
theorem signature_bit (S : Fin 3 → Finset V) (x : V) (i : Fin 3) :
    bit (signature S x) i=decide (x∈S i) := encode_bit _ _

/-- The chosen side at coordinate i consists of vertices whose membership differs from b. -/
def oriented (S : Fin 3 → Finset V) (b : Fin 8) (i : Fin 3) : Finset V :=
  if bit b i then (S i)ᶜ else S i

private theorem mem_oriented (S : Fin 3 → Finset V) (b : Fin 8) (i : Fin 3) (x : V) :
    x∈oriented S b i ↔ bit (signature S x) i≠bit b i := by
  rw [signature_bit]
  cases h : bit b i <;> simp [oriented,h]

private theorem sum_columns (S : Fin 3 → Finset V) :
    (∑ i, (S i).card)=∑ x : V,(univ.filter (fun i : Fin 3 => x∈S i)).card := by
  classical
  have left (i : Fin 3) : (S i).card=∑ x : V, if x∈S i then 1 else 0 := by simp
  simp_rw [left]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  simp [←sum_filter]

/-- For three odd cuts with a common exterior point, failure occurs precisely when
one can orient the cuts so that their three chosen sides are pairwise disjoint. -/
theorem crossing_or_disjoint (S : Fin 3 → Finset V) (a : V) (out : ∀ i,a∉S i)
    (odd : ∀ i,(S i).card%2=1) :
    (∃ u v,∀ i,WildCuts.Cross (S i) u v) ∨
      (∃ b : Fin 8,∀ i j : Fin 3,i≠j → Disjoint (oriented S b i) (oriented S b j)) := by
  classical
  let P := (univ : Finset V).image (signature S)
  have zero : 0∈P := by
    have eq : signature S a=0 := by simp [signature,encode,out]
    exact eq ▸ mem_image_of_mem _ (mem_univ a)
  rcases cube P with h|⟨i,h⟩|⟨p,hp,q,hq,h⟩|⟨b,h⟩|h
  · exact (h zero).elim
  · have pos := odd i
    obtain ⟨x,hx⟩ := card_pos.mp (show 0<(S i).card by omega)
    have f := h _ (mem_image_of_mem (signature S) (mem_univ x))
    simp [signature_bit,hx] at f
  · obtain ⟨x,_,rfl⟩ := mem_image.mp hp
    obtain ⟨y,_,rfl⟩ := mem_image.mp hq
    refine Or.inl ⟨x,y,fun i => ?_⟩
    have at_i := h i
    by_cases hx : x∈S i <;> by_cases hy : y∈S i <;> simp_all [signature_bit,WildCuts.Cross]
  · refine Or.inr ⟨b,fun i j ij => disjoint_left.mpr (fun x hx hy => ?_)⟩
    exact ij (h _ (mem_image_of_mem _ (mem_univ x)) i j
      ((mem_oriented _ _ _ _).mp hx) ((mem_oriented _ _ _ _).mp hy))
  · have e (x : V) : (univ.filter (fun i : Fin 3 => x∈S i)).card%2=0 := by
      have z := h _ (mem_image_of_mem (signature S) (mem_univ x))
      simpa [evenWeight,signature_bit] using z
    have twice : ∑ x : V,(univ.filter (fun i : Fin 3 => x∈S i)).card =
        2*∑ x : V,(univ.filter (fun i : Fin 3 => x∈S i)).card/2 := by
      rw [mul_sum]
      apply sum_congr rfl
      intro x _
      have hx := e x
      omega
    have counts := sum_columns S
    rw [twice] at counts
    simp [Fin.sum_univ_succ] at counts
    have x := odd 0
    have y := odd 1
    have z := odd 2
    omega

theorem crossing_iff (S : Fin 3 → Finset V) (a : V) (out : ∀ i,a∉S i)
    (odd : ∀ i,(S i).card%2=1) :
    (∃ u v,∀ i,WildCuts.Cross (S i) u v) ↔
      ¬∃ b : Fin 8,∀ i j : Fin 3,i≠j → Disjoint (oriented S b i) (oriented S b j) := by
  classical
  constructor
  · rintro ⟨x,y,h⟩ ⟨b,dis⟩
    have cover (i : Fin 3) : x∈oriented S b i ∨ y∈oriented S b i := by
      have hi := h i
      cases e : bit b i <;> simp [oriented,e,WildCuts.Cross] at * <;> tauto
    have sep {i j : Fin 3} (ne : i≠j) {v : V} (hi : v∈oriented S b i) (hj : v∈oriented S b j) : False :=
      disjoint_left.mp (dis i j ne) hi hj
    rcases cover 0 with h0|h0 <;> rcases cover 1 with h1|h1 <;> rcases cover 2 with h2|h2
    all_goals first | exact sep (by decide : (0 : Fin 3)≠1) h0 h1 |
      exact sep (by decide : (1 : Fin 3)≠2) h1 h2 | exact sep (by decide : (0 : Fin 3)≠2) h0 h2
  · intro h
    exact (crossing_or_disjoint S a out odd).resolve_right h

/-- Three different split colors, or more colors inducing only these three sides.
This test decides whether the single freed edge repairs this particular contraction. -/
theorem graph_iff {n : Nat} (g : Coloring (n+1) n) {w : Lines (n+1)} (win : Works g w)
    (a : Fin n) (hn : n%2=1) (cs : Fin 3 → Fin n)
    (split : ∀ i,(far g w a (cs i)).Nonempty)
    (cover : ∀ S∈sides g w a, ∃ i,S=far g w a (cs i)) :
    (∃ u v,Works (restrict g) (repair (shrink a w) u v)) ↔
      ¬∃ b : Fin 8,∀ i j : Fin 3,i≠j →
        Disjoint (oriented (fun i => far g w a (cs i)) b i) (oriented (fun i => far g w a (cs i)) b j) := by
  classical
  let S := fun i => far g w a (cs i)
  have mem (i : Fin 3) : S i∈sides g w a := mem_erase.mpr
    ⟨nonempty_iff_ne_empty.mp (split i),mem_image_of_mem _ (mem_univ (cs i))⟩
  rw [←crossing_iff S a (fun i h => mem_far.mp h (.stay _)) (fun i => odd_far g win a _ hn (split i))]
  constructor
  · rintro ⟨x,y,h⟩
    exact ⟨x,y,fun i => (repair_iff g win a x y).mp h _ (mem i)⟩
  · rintro ⟨x,y,h⟩
    refine ⟨x,y,(repair_iff g win a x y).mpr (fun s hs => ?_)⟩
    obtain ⟨i,rfl⟩ := cover s hs
    exact h i

#print axioms graph_iff
end WildExact.RootContraction.ThreeCuts
