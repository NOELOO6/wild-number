import GroupingTools
import NineData

namespace WildExact.Four
open WildExact

noncomputable def graphEdge (g : Coloring 13 13) (c : V) (a b : V) := decide (a≠b ∧ g.paint a b=c)
noncomputable def graphStar (g : Coloring 13 13) (c a : V) := decide (missingColor g a=c)

theorem row_reads (g : Coloring 13 13) (c : V) (r : Row 13) (mem : r∈Rows 13)
    (res : Respects (mate (augment (by decide) g) c) r) :
    ordinary r = graphEdge g c ∧ star r = graphStar g c := by
  constructor
  · funext a b
    by_cases same : a=b
    · simp [ordinary,graphEdge,same]
    · have h := row_equiv _ c r mem res a.castSucc b.castSucc (fun e => same (Fin.castSucc_injective _ e))
      simp [ordinary,graphEdge,same,h,augment_paint]
  · funext a
    rw [star,row_equiv _ c r mem res a.castSucc (Fin.last 13) (Fin.ne_of_lt (Fin.castSucc_lt_last _))]
    simp only [graphStar,augment,Fin.lastCases_last,Fin.lastCases_castSucc]

def trials : List V := (List.finRange 13).drop 3
def prices : List (Price 13) :=
  [((0,1),3),((0,2),3),((1,2),3),((0,13),2),((1,13),2),((2,13),2)]

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem trial_price : (Rows 13).all (fun r => !clean r || decide
    (totalI trials (fun v => score (ordinary r) (star r) 0 1 2 v) ≤ fee prices r)) = true := by
  native_decide

noncomputable def weight (g : Coloring 13 13) (v : V) :=
  totalI (List.finRange 13) fun c => score (graphEdge g c) (graphStar g c) 0 1 2 v

/-- A four-point set with six different internal colors and at most one color
whose missing point and an edge of that color both lie in the set. -/
theorem normalize_four (g : Coloring 13 13) :
    ∃ g' : Coloring 13 13, weight g' 3 < 2 ∧ (∀ b, Upper g' b → Upper g b) := by
  obtain ⟨p,good⟩ := normalize_three (by decide) (by decide) g
  let h := renamed p g
  obtain ⟨rs,hr⟩ := choose_rows (augment (by decide) h)
  have lim (c : V) : totalI trials (fun v => score (graphEdge h c) (graphStar h c) 0 1 2 v)
      ≤ fee prices (rs c) := by
    obtain ⟨ee,ss⟩ := row_reads h c _ (hr c).1 (hr c).2
    have cl := clean_row (by decide) h good (by decide) c _ (hr c).1 (hr c).2
    have test := List.all_eq_true.mp trial_price _ (hr c).1
    simpa [cl,ee,ss] using test
  have summed := total_mono (List.finRange 13) (fun c _ => lim c)
  rw [fees_sum _ _ hr prices (by decide)] at summed
  have low : totalI trials (weight h) < (trials.length:Int)*2 := by
    unfold weight
    rw [transpose]
    exact lt_of_le_of_lt summed (by decide)
  obtain ⟨v,hv,ok⟩ := some_below trials _ 2 low
  let q := Equiv.swap (3:V) v
  have room : ∀ u∈trials, u≠0 ∧ u≠1 ∧ u≠2 := by decide
  obtain ⟨n0,n1,n2⟩ := room v hv
  have q0 : q 0=0 := Equiv.swap_apply_of_ne_of_ne (by decide) n0.symm
  have q1 : q 1=1 := Equiv.swap_apply_of_ne_of_ne (by decide) n1.symm
  have q2 : q 2=2 := Equiv.swap_apply_of_ne_of_ne (by decide) n2.symm
  have q3 : q 3=v := Equiv.swap_apply_left ..
  refine ⟨renamed q h,?_,fun b up => upper_back p g (upper_back q h up)⟩
  have re (c a b : V) : graphEdge (renamed q h) c a b = graphEdge h c (q a) (q b) := by
    simp [graphEdge,renamed]
  have st (c a : V) : graphStar (renamed q h) c a = graphStar h c (q a) := by
    simp [graphStar,renamed_missing]
  simpa only [weight,score,paired,marked,re,st,q0,q1,q2,q3] using ok

#print axioms normalize_four
end WildExact.Four
