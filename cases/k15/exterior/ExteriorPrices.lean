import ExteriorData
namespace WildExterior
open Finset
set_option maxRecDepth 100000
set_option maxHeartbeats 0
-- Compute the outside triples directly. Each color contributes at most four.
private def taps : List (Option Port) := none :: (List.finRange 9).map some
private theorem checked : (rows.filter (fun p => taps.all (fun u => decide (admissible p u → RowOK p u))=false))=∅ := by native_decide

theorem row_prices {p : Pairs} {u : Option Port} (valid : p∈rows) (tap : admissible p u) :
    RowOK p u := by
  have m : u∈taps := by cases u <;> simp [taps]
  have pass : taps.all (fun u => decide (admissible p u → RowOK p u))=true := by
    cases eq : taps.all (fun u => decide (admissible p u → RowOK p u))
    · exact False.elim ((eq_empty_iff_forall_not_mem.mp checked) p (mem_filter.mpr ⟨valid,eq⟩))
    · rfl
  exact of_decide_eq_true (List.all_eq_true.mp pass u m) tap
end WildExterior
