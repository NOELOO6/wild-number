import SixCounts

namespace WildSieve.Thirty.Graph
open Finset

abbrev V := Fin 30
abbrev C := Fin 29

local instance (priority := 2000) vertexEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq

abbrev labeled := @SixCounts.labeled 30 29
abbrev full_pairs := @SixCounts.full_pairs 30 29
abbrev all_labels := @SixCounts.all_labels 30 29
abbrev inside_window := @SixCounts.inside_window 30 29
private abbrev chord := @SixCounts.chord 30 29
private abbrev tangent := @SixCounts.tangent 30 29

theorem labels_le_18 (F : Factor V C) (U : Finset V) (size : U.card=18) :
    labeled F U≤942 := by
  have h := chord F U 18 6 243 83 size (by decide)
  change 6*labeled F U+7047≤12699 at h
  omega

theorem labels_le_21 (F : Factor V C) (U : Finset V) (size : U.card=21) :
    labeled F U≤1480 := by
  have h := chord F U 21 4 520 100 size (by decide)
  change 4*labeled F U+15080≤21000 at h
  omega

theorem labels_le_24 (F : Factor V C) (U : Finset V) (size : U.card=24) :
    labeled F U≤3116 := by
  have h := chord F U 24 3 972 136 size (by decide)
  change 3*labeled F U+28188≤37536 at h
  omega

theorem labels_ge_24 (F : Factor V C) (U : Finset V) (size : U.card=24)
    (c : C) (cl : Closed (F.f c) U) : 3004≤labeled F U := by
  have h := tangent F U 24 36 240 28 size c cl (by decide) (by decide)
  change 9964≤labeled F U+6960 at h
  omega

noncomputable abbrev owners := @SixCounts.owners 30 29
noncomputable abbrev extra := @SixCounts.extra 30 29
noncomputable abbrev defect := @SixCounts.defect 30 29
theorem owner_mem {F : Factor V C} {Q : Finset V} {c : C} :
    c∈owners F Q ↔ Closed (F.f c) Q := SixCounts.owner_mem

abbrev mark_tally := @SixCounts.mark_tally 30 29
abbrev extra_tally := @SixCounts.extra_tally 30 29
abbrev marks_le_labeled := @SixCounts.marks_le_labeled 30 29
abbrev full_defect := @SixCounts.full_defect 30 29
abbrev closed_complement := @SixCounts.closed_complement 30 29

theorem disjoint_count (F : Factor V C) :
    (marks F univ).card*3004≤(∑ T∈marks F univ,(marks F Tᶜ).card)+3116*defect F :=
  SixCounts.disjoint_count F 3004 3116 (labels_le_24 F) (labels_ge_24 F)

end WildSieve.Thirty.Graph
