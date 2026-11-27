import PaletteData
namespace WildPalette
open Finset
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem rows_checked : (List.range labels.size).all (fun r => decide (regular r ∧ original r))=true := by native_decide
private theorem palettes_checked : (((univ : Finset C).powersetCard 4).filter (fun P =>
    ¬(index[code P]!<labels.size ∧ shared (index[code P]!) P)))=∅ := by native_decide

theorem four_checked (P : Finset C) (sz : P.card=4) :
    let r := index[code P]!
    regular r ∧ original r ∧ shared r P := by
  have ins := mem_powersetCard.mpr (show P⊆univ ∧ P.card=4 from ⟨subset_univ _,sz⟩)
  have yes : index[code P]!<labels.size ∧ shared (index[code P]!) P := by
    by_contra no
    exact (eq_empty_iff_forall_not_mem.mp palettes_checked) P (mem_filter.mpr ⟨ins,no⟩)
  obtain ⟨lt,share⟩ := yes
  obtain ⟨shape,base⟩ := of_decide_eq_true (List.all_eq_true.mp rows_checked _ (List.mem_range.mpr lt))
  exact ⟨shape,base,share⟩

theorem mask_exists : ∀ f : G → Bool,f 6=false → ∃ s : Cut,∀ j : G,s.val.testBit j.val=f j := by native_decide
end WildPalette
