import AnchorExample
import Lean.Data.Json.Parser
import Lean.Data.Json.FromToJson

namespace WildSieve.AnchorPacking
open Finset WildExact
local instance (priority := 2000) {m : Nat} : DecidableEq (Fin m) :=
  (inferInstance : LinearOrder (Fin m)).toDecidableEq
set_option maxRecDepth 10000

private def mates : Array (Array Nat) :=
  let data := do
    let obj ← Lean.Json.parse (include_str "example.json")
    Lean.fromJson? (← obj.getObjVal? "mates")
  data.toOption.getD #[]

private def partner (c : Fin 15) (x : Fin 16) : Fin 16 := Fin.ofNat' 16 ((mates[c.val]!)[x.val]!)
private def paint (x y : Fin 16) : Fin 15 :=
  Fin.ofNat' 15 (mates.findIdx (fun row => row[x.val]! == y.val))

def exampleColoring : Coloring 16 15 where
  paint := paint
  symm := by native_decide
  proper := by native_decide

private theorem partner_ok : ∀ c x, x≠partner c x ∧ paint x (partner c x)=c := by native_decide

private theorem restored (c x) :
    (coloringFactor (augment (by decide) (restrict exampleColoring))).f c x=partner c x := by
  change mate (augment _ _) c x=_
  rw [mate_augment_restrict]
  exact exampleColoring.proper _ _ _ (mate_spec _ _ _).1 (partner_ok c x).1
    ((mate_spec _ _ _).2.trans (partner_ok c x).2.symm)

private theorem six_distinct : ∀ c,(lowerEnds (partner c) anchor).card≤1 := by native_decide

private theorem passes : ∀ T∈testedTriples,∀ D∈choices anchor 15 3 4 1,∀ c : Fin 15,
    ∃ x∈D ∪ T.map (emb anchor),partner c x∉D ∪ T.map (emb anchor) := by native_decide

theorem catalog_size : testedTriples.card=142 := by native_decide

/-- The packing alone certifies ten wild edges for the supplied coloring. -/
theorem example_exact : Exact (restrict exampleColoring) 10 := by
  apply ten_from_packing
  · intro c
    change (lowerEnds _ anchor).card≤1
    rw [show (coloringFactor (augment _ (restrict exampleColoring))).f c=partner c from funext (restored c)]
    exact six_distinct c
  · have empty : testedTriples∩badScopes (coloringFactor (augment (by decide) (restrict exampleColoring))) anchor 15 3 4 1=∅ := by
      apply eq_empty_iff_forall_not_mem.mpr
      intro T ht
      obtain ⟨test,bad⟩ := mem_inter.mp ht
      obtain ⟨D,hd,cut⟩ := (mem_gather _ _ _).mp bad
      obtain ⟨_,c,cl⟩ := pull_mem.mp cut
      obtain ⟨x,xin,xout⟩ := passes T test D hd c
      exact xout (restored c x ▸ cl x xin)
    simp [empty]

#print axioms example_exact
end WildSieve.AnchorPacking
