import CyclicCertificate
import LowerBound
namespace K19Rotation
open EdgeWalk WildDeletion
set_option interpreter.prefer_native true
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def edgeNumber (e : Edge 19) := 19*max e.1.val e.2.val + min e.1.val e.2.val
def legalWild (w : Edges) := w.all (fun e => e.1 != e.2) && (w.map edgeNumber).eraseDups.length == w.length
theorem legal_choices : rows.all (fun p => legalWild (layouts[p.2]?.getD [])) = true := by native_decide

/-- In the same graph model, 13 distinct ordinary edges suffice and every
connecting set of ordinary edges has length at least 13. -/
theorem exact_rotational_wild_number (s : Edges) (hs : Starter points.tail [] s) (hn : s.length = 9)
    (g : WildLower.Coloring V) (represents : ∀ c, g.edges c = shifted s c) :
    (∃ w : Edges, legalWild w = true ∧ w.length = 13 ∧ ∀ c, Connected (Adj (w ++ g.edges c))) ∧
    ∀ w : Edges, (∀ e ∈ w, e.1 ≠ e.2) →
      (∀ c, Connected (Adj (w ++ g.edges c))) → 13 ≤ w.length := by
  refine ⟨?_,fun w lines h => WildLower.thirteen_necessary g w lines h⟩
  have mem : s ∈ starters := exhaustive hs 9 (by omega)
  rw [← all_listed] at mem
  obtain ⟨⟨t,i⟩,hi,eq⟩ := List.mem_map.mp mem
  change t = s at eq
  subst t
  have good := List.all_eq_true.mp legal_choices (s,i) hi
  obtain ⟨len,ok⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp checked (s,i) hi)
  refine ⟨_,good,beq_iff_eq.mp len,fun c => ?_⟩
  rw [represents]
  exact connected_of_passes 0 _ (List.all_eq_true.mp ok c (by revert c; decide))
#print axioms exact_rotational_wild_number
end K19Rotation
