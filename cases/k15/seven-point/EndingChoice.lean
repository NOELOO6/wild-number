import ExteriorEligibility
import OutsideNames
import SixTrap

namespace EndingChoice
open VertexRedraw EdgeWalk WildDeletion ExteriorRows

/-- Point 15 in a label denotes the unchanged outside list. -/
abbrev Label := Nat × Nat

def prescribed (label : Label) (x : V) : C :=
  if x.val = label.1 then Fin.ofNat' 15 label.2 else InsideNames.missing x

def eligible (label : Label) : Bool :=
  let cs := nine.map (prescribed label)
  decide cs.Nodup && required.all cs.contains &&
    nine.all (fun x => (pricesAt x).contains (prescribed label x))

def oneChange := nine.flatMap fun x => colors.filterMap fun c =>
  let label := (x.val,c.val)
  if c != InsideNames.missing x && eligible label then some label else none

def budgetAt (label : Label) (j : Fin 280) :=
  let cs := nine.map (prescribed label)
  budget (fun c => ((cs.idxOf? c).map (·+1)).getD 0) j

structure Drawing where
  win : List Nat
  rows : List (Array Nat)
  deriving Inhabited

structure Family where
  label : Label
  picks : Array Nat
  drawings : Array Drawing
  deriving Inhabited

def parseFamily (s : String) : Family :=
  let blocks := s.splitOn "\n\n"
  let header := numbers blocks.head!
  ⟨(header[0]![0]!, header[0]![1]!), header[1]!.toArray,
    (blocks.tail.map fun block =>
      let ns := numbers block
      Drawing.mk ns.head! (ns.tail.map List.toArray)).toArray⟩

def families := ((include_str "ending-drawings.txt").trim.splitOn "\n\n\n").map parseFamily

def mate (d : Drawing) (c : C) (x : V) : V := Fin.ofNat' 16 d.rows[c.val]![x.val]!
def ordinary (d : Drawing) := colors.map fun c => actualEdges (mate d c)

def fitsFamily (label : Label) (d : Drawing) :=
  properRows d.rows && d.rows.all (fun m => SixTrap.edgesInside FixedSix.seven m ≤ 2) &&
  nine.all (fun x => mate d (prescribed label x) 15 == x) &&
  colors.all (fun c => nine.all (fun x => !outside (SixBoundary.ref c x) ||
    mate d c x == SixBoundary.ref c x))

def ending (j : Fin 280) := FixedSix.endings[j.val]!
def selected (f : Family) (j : Fin 280) := f.drawings[f.picks[j.val]!]!

def checked (f : Family) :=
  f.picks.size == 280 && f.picks.all (· < f.drawings.size) &&
  f.drawings.all (fun d => fitsFamily f.label d && FixedSix.all.contains d.win &&
    decide (SixTrap.classify (trial d.win) (ordinary d) = .win)) &&
  ends.all (fun j =>
    let es := ordinary (selected f j)
    FixedSix.starts.all fun a => decide (SixTrap.classify (trial (a ++ ending j)) es = .loss))

def cheapLabels : List Label := [(10,2), (10,14)]

theorem inventory :
    oneChange.length = 13 ∧
    families.map Family.label = (15,0) :: oneChange.filter (fun p => !cheapLabels.contains p) ∧
    (oneChange.filter (fun p => cheapLabels.contains p)) = cheapLabels ∧
    (∀ p ∈ cheapLabels, budgetAt p 106 < 10) ∧
    (families.map (fun f => f.drawings.size)).sum = 207 := by native_decide

set_option maxRecDepth 100000 in
theorem drawing_checks : families.all checked = true := by native_decide

/-- Once the outside triples are specified, a proper drawing with the prescribed
outside edges and missing colors defeats all ten inside splits. The same drawing
has a connected grouping among the full 2,800. -/
theorem chosen_ending_can_lose (label : Label)
    (h : label = (15,0) ∨ (label ∈ oneChange ∧ label ∉ cheapLabels))
    (b : List Nat) (hb : b ∈ FixedSix.endings) :
    ∃ d : Drawing, fitsFamily label d = true ∧ d.win ∈ FixedSix.all ∧
      (∀ m ∈ ordinary d, Connected (Adj (trial d.win ++ m))) ∧
      ∀ a ∈ FixedSix.starts, ∃ m ∈ ordinary d, ¬ Connected (Adj (trial (a ++ b) ++ m)) := by
  have listed : label ∈ families.map Family.label := by
    rw [inventory.2.1]
    rcases h with rfl | ⟨mem, hard⟩
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨mem, by simpa using hard⟩)
  obtain ⟨f,hf,eq⟩ := List.mem_map.mp listed
  have enumerated : ends.map ending = FixedSix.endings := by native_decide
  rw [← enumerated] at hb
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hb
  have ok := Bool.and_eq_true_iff.mp (List.all_eq_true.mp drawing_checks f hf)
  obtain ⟨bounds, valid⟩ := Bool.and_eq_true_iff.mp ok.1
  obtain ⟨size, ids⟩ := Bool.and_eq_true_iff.mp bounds
  have inPicks : j.val < f.picks.size := by rw [beq_iff_eq.mp size]; exact j.isLt
  have ix := Array.all_eq_true_iff_forall_mem.mp ids (f.picks[j.val]) (Array.getElem_mem inPicks)
  have inDraws : f.picks[j.val]! < f.drawings.size := by
    rw [getElem!_pos f.picks j.val inPicks]
    exact of_decide_eq_true ix
  have drawn : selected f j ∈ f.drawings := by
    unfold selected
    rw [getElem!_pos f.drawings (f.picks[j.val]!) inDraws]
    exact Array.getElem_mem inDraws
  have detail := Bool.and_eq_true_iff.mp (Array.all_eq_true_iff_forall_mem.mp valid _ drawn)
  obtain ⟨matchesLabel,winningGroup⟩ := Bool.and_eq_true_iff.mp detail.1
  refine ⟨selected f j, eq ▸ matchesLabel, List.contains_iff_mem.mp winningGroup,
    SixTrap.win_connected (of_decide_eq_true detail.2), ?_⟩
  intro a ha
  have loses := List.all_eq_true.mp (List.all_eq_true.mp ok.2 j hj) a ha
  exact SixTrap.loss_disconnected (of_decide_eq_true loses)

#print axioms chosen_ending_can_lose
end EndingChoice
