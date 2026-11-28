import GraphCycles24
import Mathlib.Data.Multiset.Powerset

namespace WildSieve.TwentyFour
open Finset WildAnchor WildExact
local instance (priority := 2000) halfEq {n : Nat} : DecidableEq (Fin n) := (inferInstance : LinearOrder (Fin n)).toDecidableEq

private def atBit {m : Nat} (b : Bool) : Fin m ↪ Point m :=
  ⟨fun i => (i,b),fun _ _ h => congrArg Prod.fst h⟩

def halves {m : Nat} (X Y : Finset (Fin m)) := X.map (atBit false) ∪ Y.map (atBit true)

@[simp] theorem mem_halves {m : Nat} (X Y : Finset (Fin m)) (i : Fin m) (b : Bool) :
    (i,b)∈halves X Y ↔ i∈(if b then Y else X) := by
  cases b <;> simp [halves,atBit]

theorem halves_size {m : Nat} (X Y : Finset (Fin m)) : (halves X Y).card=X.card+Y.card := by
  have dis : Disjoint (X.map (atBit false)) (Y.map (atBit true)) := by
    apply disjoint_left.mpr
    rintro _ hx hy
    obtain ⟨a,_,rfl⟩ := mem_map.mp hx
    obtain ⟨b,_,eq⟩ := mem_map.mp hy
    exact Bool.noConfusion (congrArg Prod.snd eq)
  simp only [halves,card_union_of_disjoint dis,card_map]

def halvesEquiv (m : Nat) : (Finset (Fin m) × Finset (Fin m)) ≃ Finset (Point m) where
  toFun z := halves z.1 z.2
  invFun S := (univ.filter (fun i => (i,false)∈S),univ.filter (fun i => (i,true)∈S))
  left_inv := by rintro ⟨X,Y⟩; apply Prod.ext <;> ext <;> simp
  right_inv := by intro S; ext ⟨i,b⟩; cases b <;> simp

theorem paired_halves {m : Nat} (p : Equiv.Perm (Fin m)) (X Y : Finset (Fin m)) :
    (pairedIndices p (halves X Y)).card=(Y∩X.map p.toEmbedding).card := by
  apply card_bij (fun i _ => p i)
  · intro i h
    obtain ⟨hx,hy⟩ := (mem_filter.mp h).2
    simp only [mem_halves,Bool.false_eq_true,if_true,if_false] at hx hy
    exact mem_inter.mpr ⟨hy,mem_map.mpr ⟨i,hx,rfl⟩⟩
  · exact fun _ _ _ _ eq => p.injective eq
  · intro i h
    obtain ⟨hy,hx⟩ := mem_inter.mp h
    obtain ⟨j,hj,rfl⟩ := mem_map.mp hx
    exact ⟨j,mem_filter.mpr ⟨mem_univ _,by simpa using hj,by simpa using hy⟩,rfl⟩

/-- A selected true endpoint contributes one to each matching for which
its adjacent false endpoint belongs to X. -/
def edgeBits {m : Nat} (p : Equiv.Perm (Fin m)) (X : Finset (Fin m)) (i : Fin m) : Bool × Bool :=
  (decide (i∈X),decide (i∈X.map p.toEmbedding))

def totals (Z : Multiset (Bool × Bool)) : Nat × Nat :=
  (Z.countP (fun v => v.1=true),Z.countP (fun v => v.2=true))

private theorem tags_on_subset {m : Nat} (p : Equiv.Perm (Fin m)) (X Y : Finset (Fin m)) :
    totals (Y.val.map (edgeBits p X))=((Y∩X).card,(Y∩X.map p.toEmbedding).card) := by
  apply Prod.ext <;> simp only [totals,Multiset.countP_eq_card_filter,Multiset.filter_map,Multiset.card_map]
  · change (Y.filter _).card=_
    congr 1
    ext i
    simp [edgeBits,Function.comp_def]
  · change (Y.filter _).card=_
    congr 1
    ext i
    simp [edgeBits,Function.comp_def]

/-- Conditional on the false half of the subset, the multiset of both
internal-edge counts among all v-point true halves depends only on the
four endpoint types, including all their multiplicities. -/
theorem subset_profile {m : Nat} (p : Equiv.Perm (Fin m)) (X : Finset (Fin m)) (v : Nat) :
    ((univ : Finset (Fin m)).powersetCard v).val.map
      (fun Y => ((Y∩X).card,(Y∩X.map p.toEmbedding).card)) =
    (((univ : Finset (Fin m)).val.map (edgeBits p X)).powersetCard v).map totals := by
  rw [Multiset.powersetCard_map,←Finset.map_val_val_powersetCard]
  simp only [Multiset.map_map]
  apply Multiset.map_congr rfl
  intro Y _
  exact (tags_on_subset p X Y).symm

/-- The complete joint spectrum of a pair of actual colors is obtained by
choosing the two subsets of twelve indices independently. -/
theorem two_color_spectrum (g : Coloring 24 23) (a c : Fin 23) (ne : c≠a) :
    ∃ cs∈shapes,∃ e : (Finset (Fin 12) × Finset (Fin 12)) ≃ Finset (Fin 24),
      ∀ X Y, (e (X,Y)).card=X.card+Y.card ∧
        Inside (coloringFactor g) a (e (X,Y))=(Y∩X).card ∧
        Inside (coloringFactor g) c (e (X,Y))=(Y∩X.map (cyclePerm 12 cs).toEmbedding).card := by
  obtain ⟨cs,h,w,chart⟩ := chart_of_colors g a c ne
  refine ⟨cs,h,(halvesEquiv 12).trans (Equiv.finsetCongr w),?_⟩
  intro X Y
  change ((halves X Y).map w.toEmbedding).card=_ ∧ _ ∧ _
  obtain ⟨left,right⟩ := chart (halves X Y)
  refine ⟨by rw [card_map,halves_size],?_,right.trans (paired_halves _ _ _)⟩
  simpa using left.trans (paired_halves (Equiv.refl _) X Y)

#print axioms two_color_spectrum
end WildSieve.TwentyFour
