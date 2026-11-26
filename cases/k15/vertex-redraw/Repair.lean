import Outside
namespace VertexRedraw
open EdgeWalk WildDeletion
def isolates (s : Nat) (es : E) :=
  (List.finRange 15).any (fun v => s.testBit v.val) &&
  (List.finRange 15).any (fun v => !s.testBit v.val) &&
  es.all (fun e => s.testBit e.1.val == s.testBit e.2.val)
private theorem no_path {s es} (iso : isolates s es=true) : ¬Connected (Adj es) := by
  obtain ⟨points,edges⟩ := Bool.and_eq_true_iff.mp iso
  obtain ⟨yes,no⟩ := Bool.and_eq_true_iff.mp points
  obtain ⟨x,_,hx⟩ := List.any_eq_true.mp yes
  obtain ⟨y,_,hy⟩ := List.any_eq_true.mp no
  have same {i j : Fin 15} (p : Walk (Adj es) i j) : s.testBit i.val=s.testBit j.val := by
    induction p with
    | stay => rfl
    | step _ edge ih =>
      apply ih.trans
      rcases edge with h|h
      · exact beq_iff_eq.mp (List.all_eq_true.mp edges _ h)
      · exact (beq_iff_eq.mp (List.all_eq_true.mp edges _ h)).symm
  intro connected
  have eq := same (connected x y)
  simp_all

def blocked (g : List Nat) (c : C) := (g ++ Teams.unorderedPairs g (· ||| ·)).any
  (fun s => isolates s (trial g ++ actualEdges (partner c)))
private theorem disconnected {g c} (h : blocked g c=true) :
    ¬Connected (Adj (trial g ++ actualEdges (partner c))) := by
  obtain ⟨_,_,iso⟩ := List.any_eq_true.mp h
  exact no_path iso
theorem recorded : blocked start 12=true ∧
    ((swaps start).all fun g => colors.any (blocked g))=true ∧
    (colors.all fun c => decide (c=12) || passes 0 (trial start ++ actualEdges (partner c)))=true := by native_decide

theorem start_only_twelve (c : C) :
    Connected (Adj (trial start ++ actualEdges (partner c))) ↔ c≠12 := by
  constructor
  · rintro yes rfl; exact disconnected recorded.1 yes
  · intro ne
    have h := List.all_eq_true.mp recorded.2.2 c ((by decide : ∀ i:C,i∈colors) c)
    exact connected_of_passes 0 _ (by simpa [ne] using h)
private theorem middle_record : blocked middle 12=true ∧
    (colors.all fun c => decide (c=12) || passes 0 (trial middle ++ actualEdges (partner c)))=true := by native_decide
theorem middle_only_twelve (c : C) :
    Connected (Adj (trial middle ++ actualEdges (partner c))) ↔ c≠12 := by
  constructor
  · rintro yes rfl; exact disconnected middle_record.1 yes
  · intro ne
    have h := List.all_eq_true.mp middle_record.2 c ((by decide : ∀ i:C,i∈colors) c)
    exact connected_of_passes 0 _ (by simpa [ne] using h)

theorem no_single_swap (g : List Nat) (h : g∈swaps start) :
    ∃ c : C, ¬Connected (Adj (trial g ++ actualEdges (partner c))) := by
  obtain ⟨c,_,hc⟩ := List.any_eq_true.mp (List.all_eq_true.mp recorded.2.1 g h)
  exact ⟨c,disconnected hc⟩
#print axioms no_single_swap
end VertexRedraw
