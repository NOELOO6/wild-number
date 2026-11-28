import SixCounts36

namespace WildSieve.ThirtySix
open Finset
local instance (priority := 2000) ownersVertexEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq

noncomputable abbrev owners := @SixCounts.owners 36 35
noncomputable abbrev extra := @SixCounts.extra 36 35
noncomputable abbrev defect := @SixCounts.defect 36 35
theorem owner_mem {F : Factor V C} {Q : Finset V} {c : C} :
    c∈owners F Q ↔ Closed (F.f c) Q := SixCounts.owner_mem

abbrev mark_tally := @SixCounts.mark_tally 36 35
abbrev extra_tally := @SixCounts.extra_tally 36 35
abbrev marks_le_labeled := @SixCounts.marks_le_labeled 36 35
abbrev full_defect := @SixCounts.full_defect 36 35
abbrev closed_complement := @SixCounts.closed_complement 36 35

theorem disjoint_count (F : Factor V C) :
    (marks F univ).card*8727≤(∑ T∈marks F univ,(marks F Tᶜ).card)+8875*defect F :=
  SixCounts.disjoint_count F 8727 8875 (labels_le_30 F) (labels_ge_30 F)

end WildSieve.ThirtySix
