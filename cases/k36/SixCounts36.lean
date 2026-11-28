import SixCounts

namespace WildSieve.ThirtySix
open Finset

abbrev V := Fin 36
abbrev C := Fin 35

local instance (priority := 2000) vertexEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq

abbrev labeled := @SixCounts.labeled 36 35
abbrev full_pairs := @SixCounts.full_pairs 36 35
abbrev all_labels := @SixCounts.all_labels 36 35
abbrev inside_window := @SixCounts.inside_window 36 35
private abbrev chord := @SixCounts.chord 36 35
private abbrev tangent := @SixCounts.tangent 36 35

theorem labels_le_18 (F : Factor V C) (U : Finset V) (size : U.card=18) :
    labeled F U≤1428 := by
  have h := chord F U 18 9 0 84 size (by decide)
  change 9*labeled F U+0≤12852 at h
  omega

theorem labels_le_24 (F : Factor V C) (U : Finset V) (size : U.card=24) :
    labeled F U≤2900 := by
  have h := chord F U 24 6 1080 200 size (by decide)
  change 6*labeled F U+37800≤55200 at h
  omega

theorem labels_le_27 (F : Factor V C) (U : Finset V) (size : U.card=27) :
    labeled F U≤4758 := by
  have h := chord F U 27 4 1482 202 size (by decide)
  change 4*labeled F U+51870≤70902 at h
  omega

theorem labels_le_30 (F : Factor V C) (U : Finset V) (size : U.card=30) :
    labeled F U≤8875 := by
  have h := chord F U 30 3 2160 235 size (by decide)
  change 3*labeled F U+75600≤102225 at h
  omega

theorem labels_ge_24 (F : Factor V C) (U : Finset V) (size : U.card=24)
    (c : C) (cl : Closed (F.f c) U) : 1956≤labeled F U := by
  have h := tangent F U 24 21 112 80 size c cl (by decide) (by decide)
  change 5876≤labeled F U+3920 at h
  omega

theorem labels_ge_30 (F : Factor V C) (U : Finset V) (size : U.card=30)
    (c : C) (cl : Closed (F.f c) U) : 8727≤labeled F U := by
  have h := tangent F U 30 66 572 37 size c cl (by decide) (by decide)
  change 28747≤labeled F U+20020 at h
  omega

end WildSieve.ThirtySix
