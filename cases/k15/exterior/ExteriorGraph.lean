import ExteriorAccounts
import ExteriorCuts
import ExteriorNine

namespace WildExterior
open Finset WildSieve WildExact

def Clear (F : Factor V Color) (i : Port ↪ V) (r : V) (T : Finset Port) : Prop :=
  ∀ c, ¬Closed (F.f c) (insert r (T.map i)) ∧ ¬Closed (F.f c) (outside i \ T.map i)

/-- Under the seven-point rule, the two cut tests independent of the split
of the fixed six always admit an exterior partition. Four arbitrarily named
triples may be forbidden at the same time. -/
theorem exterior_graph (F : Factor V Color) (i : Port ↪ V) (r : V) (out : r∉outside i)
    (rule : ∀ c,Inside F c (outside i)ᶜ≤2) (E : Finset (Finset Port)) (four : E.card≤4) :
    ∃ L : Layout (univ : Finset Port),∀ T∈L.val,Clear F i r T ∧ T∉E := by
  obtain ⟨L,pass⟩ := exterior_layout (account_graph F i r out rule) E four
  refine ⟨L,fun T ht => ⟨?_,(pass T ht).2⟩⟩
  apply common_cuts F i r out _ T (L.property.1.size T ht) (pass T ht).1
  intro c
  rw [ordinary_gap F i rule c]
  have := rule c
  omega

def oldNine (j : Port ↪ Fin 15) : Port ↪ V := j.trans ⟨Fin.castSucc,Fin.castSucc_injective 15⟩

private theorem root_out (j : Port ↪ Fin 15) : Fin.last 15∉outside (oldNine j) := by
  rintro h
  obtain ⟨x,eq⟩ := outside_mem.mp h
  exact Fin.castSucc_ne_last (j x) eq

/-- Two different partitions can be chosen with no common triple. Both
partitions pass both common tests for every color of the original graph. -/
theorem k15_two_exteriors (g : Coloring 15 15) (j : Port ↪ Fin 15)
    (rule : ∀ c,Inside (coloringFactor (augment (by decide) g)) c (outside (oldNine j))ᶜ≤2) :
    let F := coloringFactor (augment (by decide) g)
    ∃ L M : Layout (univ : Finset Port),Disjoint L.val M.val ∧
      (∀ T∈L.val,Clear F (oldNine j) (Fin.last 15) T) ∧
      (∀ T∈M.val,Clear F (oldNine j) (Fin.last 15) T) := by
  let F := coloringFactor (augment (by decide) g)
  have go := exterior_graph F (oldNine j) (Fin.last 15) (root_out j) rule
  obtain ⟨L,hL⟩ := go ∅ (by decide)
  have sz := L.property.1.card_vertices
  rw [L.property.2,card_univ,Fintype.card_fin] at sz
  obtain ⟨M,hM⟩ := go L.val (by omega)
  exact ⟨L,M,disjoint_left.mpr (fun {T} ht hm => (hM T hm).2 ht),
    fun T ht => (hL T ht).1,fun T ht => (hM T ht).1⟩

#print axioms exterior_graph
#print axioms k15_two_exteriors
end WildExterior
