import HalfTable24

namespace WildSieve.TwentyFour
open Finset WildAnchor WildExact
set_option maxRecDepth 6000
set_option maxHeartbeats 800000
local instance (priority := 2000) graphTableEq {n : Nat} : DecidableEq (Fin n) := (inferInstance : LinearOrder (Fin n)).toDecidableEq

def cutKey (p : Equiv.Perm (Fin 12)) (X : Finset (Fin 12)) : Fin 13 × Fin 13 :=
  (⟨X.card,by have := X.card_le_univ; simp at this; omega⟩,
   ⟨overlapSize p X,by
     have h := card_le_card (inter_subset_left : X∩X.map p.toEmbedding⊆X)
     have := X.card_le_univ
     simp at this
     dsimp [overlapSize]
     omega⟩)

def keys (cs : List Nat) := (univ : Finset (Finset (Fin 12))).val.map (cutKey (cyclePerm 12 cs))

def frequencies (cs : List Nat) :=
  let entries := keys cs
  fun x y : Fin 13 => entries.count (x,y)

private theorem count_key {α β : Type} [Fintype α] [DecidableEq β] (key : α → β) (z : β) :
    ((univ : Finset α).val.map key).count z = (univ.filter (fun a => key a=z)).card := by
  rw [Multiset.count_eq_card_filter_eq,Multiset.filter_map,Multiset.card_map]
  change ((univ : Finset α).filter (fun a => z=key a)).card=_
  apply congrArg Finset.card
  ext x
  exact (by simp only [mem_filter,mem_univ,true_and]; exact eq_comm)

private theorem frequency_at (cs : List Nat) (x y : Fin 13) :
    frequencies cs x y = (univ.filter (fun X => cutKey (cyclePerm 12 cs) X=(x,y))).card :=
  count_key _ _

def halfCell (x y u a b : Nat) :=
  if x≤u ∧ y≤x ∧ 2*x≤12+y then conditionalCell 12 x y (u-x) a b else 0

/-- Joint distribution of vertex count and the two internal-edge counts,
with false halves grouped by their overlap with their own cycle shift. -/
def referenceCell (cs : List Nat) (u a b : Nat) :=
  ∑ x : Fin 13,∑ y : Fin 13,frequencies cs x y*halfCell x y u a b

noncomputable def graphCell (g : Coloring 24 23) (a c : Fin 23) (u i j : Nat) :=
  (univ.filter (fun S : Finset (Fin 24) => S.card=u ∧
    Inside (coloringFactor g) a S=i ∧ Inside (coloringFactor g) c S=j)).card

/-- Every cell for an arbitrary pair of actual colors equals the corresponding
four-population count on one shape, simultaneously for every subset size. -/
theorem graph_reference (g : Coloring 24 23) (a c : Fin 23) (ne : c≠a) :
    ∃ cs∈shapes,∀ u i j,graphCell g a c u i j=referenceCell cs u i j := by
  classical
  obtain ⟨cs,h,e,chart⟩ := two_color_spectrum g a c ne
  refine ⟨cs,h,?_⟩
  intro u i j
  let p := cyclePerm 12 cs
  let cond (X Y : Finset (Fin 12)) := X.card+Y.card=u ∧ (Y∩X).card=i ∧ (Y∩X.map p.toEmbedding).card=j
  have cell (X) : (∑ Y : Finset (Fin 12),if cond X Y then 1 else 0)=
      halfCell X.card (overlapSize p X) u i j := by
    have cap := (X∪X.map p.toEmbedding).card_le_univ
    have add := card_union_add_card_inter X (X.map p.toEmbedding)
    have ov := card_le_card (inter_subset_left : X∩X.map p.toEmbedding⊆X)
    simp only [card_map,card_univ,Fintype.card_fin] at cap add
    have valid : overlapSize p X≤X.card ∧ 2*X.card≤12+overlapSize p X := by dsimp [overlapSize]; omega
    by_cases fit : X.card≤u
    · rw [halfCell,if_pos ⟨fit,valid⟩,←conditional_correct]
      rw [←Finset.card_filter]
      congr 1
      ext Y
      simp only [cond,mem_filter,mem_univ,true_and,mem_powersetCard,subset_univ]
      omega
    · have no (Y) : ¬cond X Y := fun q => by have := q.1; omega
      simp [no,halfCell,fit]
  let mode (X : Finset (Fin 12)) := cutKey p X
  let f (z : Fin 13 × Fin 13) := halfCell z.1 z.2 u i j
  have collect : (∑ X : Finset (Fin 12),f (mode X))=referenceCell cs u i j := by
    have fiber (z : Fin 13 × Fin 13) :
        (∑ X : Finset (Fin 12),if mode X=z then f z else 0)=frequencies cs z.1 z.2*f z := by
      rw [←sum_filter,sum_const,nsmul_eq_mul,Nat.cast_id,frequency_at]
    rw [show (∑ X : Finset (Fin 12),f (mode X))=∑ X : Finset (Fin 12),∑ z : Fin 13 × Fin 13,
          if mode X=z then f z else 0 by simp,sum_comm,sum_congr rfl (fun z _ => fiber z),Fintype.sum_prod_type]
    rfl
  change (univ.filter _).card=_
  rw [Finset.card_filter]
  let hit (S : Finset (Fin 24)) : Nat := if S.card=u ∧ Inside (coloringFactor g) a S=i ∧
    Inside (coloringFactor g) c S=j then 1 else 0
  change (∑ S,hit S)=_
  rw [←Fintype.sum_equiv e (fun z => hit (e z)) hit (fun _ => rfl),Fintype.sum_prod_type]
  have transport (X Y) : hit (e (X,Y))=if cond X Y then 1 else 0 := by
    simp only [hit,cond,p,(chart X Y).1,(chart X Y).2.1,(chart X Y).2.2]
  simp_rw [transport,cell]
  exact collect

#print axioms graph_reference
end WildSieve.TwentyFour
