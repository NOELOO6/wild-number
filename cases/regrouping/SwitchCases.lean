import SwapExamples
import OddSwitch
namespace WildExact.Regroup.SwitchCases
open EdgeWalk WildDeletion
set_option maxRecDepth 10000

private def rows := (((include_str "two-piece-k15.txt").trim.splitOn "\n").map fun line =>
  ((line.splitOn " ").filter (· != "")).map String.toNat!).toArray
private def paint (x y : Fin 15) := Fin.ofNat' 15 (rows.findIdx (fun r => r[x.val]?==some y.val))
def pivotColoring : Coloring 15 15 where
  paint := paint
  symm := by native_decide
  proper := by native_decide

def nine := [[0,1,2],[3,4,6],[5,7,8]]
def fifteen := [[0,1,2],[3,8,13],[4,5,11],[6,9,10],[7,12,14]]
def twentyOne := [[7,9,17],[11,13,14],[4,5,20],[0,2,6],[1,10,18],[15,16,19],[3,8,12]]
private def side (v : Fin 15) := v=6 ∨ v=9 ∨ v=10
private instance (v : Fin 15) : Decidable (side v) := by unfold side; infer_instance

private def tally {n} [NeZero n] (g : Coloring n n) (t : List (List Nat)) (c : Fin n) :=
  let es := layoutEdges g t c
  let piece := run es n 1
  let pairs := (List.finRange n).flatMap fun i => ((List.finRange n).filter (fun j =>
    i<j && piece.testBit i.val != piece.testBit j.val)).map (i,·)
  let after (p : Fin n × Fin n) := layoutEdges g (swapPoints p.1 p.2 t)
  (pairs.length,(pairs.filter (fun p => passes 0 (after p c))).length,
    (pairs.filter (fun p => (List.finRange n).all (fun d => passes 0 (after p d)))).length)

/-- The three counts are cross-component swaps, swaps that connect the
failed color and swaps that connect every color. -/
theorem checked_rows : tally (Periodic.roundRobin 9) nine 2=(18,18,6) ∧
    tally pivotColoring fifteen 8=(36,36,0) ∧ tally (Periodic.roundRobin 21) twentyOne 6=(108,102,36) := by native_decide

private def check {n} [NeZero n] (g : Coloring n n) (t : List (List Nat)) (c : Fin n) (z : Fin n) :=
  let es := layoutEdges g t c
  let first := run es n 1
  let second := run es n (2^z.val)
  first &&& second == 0 && (first ||| second)==2^n-1 &&
    es.all (fun e => first.testBit e.1.val==first.testBit e.2.val) &&
    (List.finRange n).all (fun d => d==c || passes 0 (layoutEdges g t d)) &&
    (List.finRange n).all (fun i => (List.finRange n).all (fun j =>
      (List.finRange n).all (fun d => let s := layoutEdges g (swapPoints i j t) d; passes 0 s || loses s)))

theorem complete_checks : check (Periodic.roundRobin 9) nine 2 3=true ∧ check pivotColoring fifteen 8 6=true ∧
    check (Periodic.roundRobin 21) twentyOne 6 3=true := by native_decide

private theorem seen : ∀ v : Fin 15,if side v then
      (run (layoutEdges pivotColoring fifteen 8) 15 (2^6)).testBit v.val=true
    else (run (layoutEdges pivotColoring fifteen 8) 15 1).testBit v.val=true := by native_decide
private theorem edges_stay : (layoutEdges pivotColoring fifteen 8).all
    (fun e => decide (side e.1 ↔ side e.2))=true := by native_decide

theorem exactly_two (a b : Fin 15) :
    Walk (Adj (layoutEdges pivotColoring fifteen 8)) a b ↔ (side a ↔ side b) := by
  let es := layoutEdges pivotColoring fifteen 8
  have sym : ∀ {x y},Adj es x y → Adj es y x := fun h => h.symm
  constructor
  · intro walk
    induction walk with
    | stay => rfl
    | step _ edge ih =>
      apply ih.trans
      rcases edge with e|e
      · exact of_decide_eq_true (List.all_eq_true.mp edges_stay _ e)
      · exact (of_decide_eq_true (List.all_eq_true.mp edges_stay _ e)).symm
  · intro same
    by_cases ha : side a
    · have hb := same.mp ha
      have obs (v : Fin 15) (yes : side v) : Walk (Adj es) 6 v :=
        walk_of_seen 6 v _ (by simpa only [if_pos yes] using seen v)
      exact (backwards sym (obs a ha)).join (obs b hb)
    · have hb : ¬side b := fun h => ha (same.mpr h)
      have obs (v : Fin 15) (no : ¬side v) : Walk (Adj es) 0 v :=
        walk_of_seen 0 v _ (by simpa only [if_neg no] using seen v)
      exact (backwards sym (obs a ha)).join (obs b hb)

private theorem repair_all : ∀ x y : Fin 15,¬(side x ↔ side y) →
    passes 0 (layoutEdges pivotColoring (swapPoints x y fifteen) 8)=true := by native_decide
private theorem spoils : ∀ x y : Fin 15,∃ c : Fin 15,loses (layoutEdges pivotColoring (swapPoints x y fifteen) c)=true := by native_decide

/-- Every cross-component swap connects color 8. All single swaps leave a
disconnected color. Swapping 0 with 4 first, then 0 with 6, succeeds. -/
theorem swap_trap :
    (∀ c : Fin 15,c≠8 → Connected (Adj (layoutEdges pivotColoring fifteen c))) ∧
    (∀ x y : Fin 15,¬(side x ↔ side y) → Connected (Adj (layoutEdges pivotColoring (swapPoints x y fifteen) 8))) ∧
    (∀ x y : Fin 15,∃ c : Fin 15,¬Connected (Adj (layoutEdges pivotColoring (swapPoints x y fifteen) c))) ∧
    (∀ c : Fin 15,c≠8 → Connected (Adj (layoutEdges pivotColoring (swapPoints (0 : Fin 15) 4 fifteen) c))) ∧
    (∀ c : Fin 15,Connected (Adj (layoutEdges pivotColoring (swapPoints (0 : Fin 15) 6 (swapPoints (0 : Fin 15) 4 fifteen)) c))) := by
  have initial : ∀ c : Fin 15,c≠8 → passes 0 (layoutEdges pivotColoring fifteen c)=true := by native_decide
  have mid : ∀ c : Fin 15,c≠8 → passes 0 (layoutEdges pivotColoring (swapPoints (0 : Fin 15) 4 fifteen) c)=true := by native_decide
  have final : ∀ c : Fin 15,passes 0 (layoutEdges pivotColoring (swapPoints (0 : Fin 15) 6 (swapPoints (0 : Fin 15) 4 fifteen)) c)=true := by native_decide
  exact ⟨fun c h => connected_of_passes 0 _ (initial c h),fun x y h => connected_of_passes 0 _ (repair_all x y h),
    fun x y => (spoils x y).imp (fun _ => lost),fun c h => connected_of_passes 0 _ (mid c h),
    fun c => connected_of_passes 0 _ (final c)⟩

private def repairingSwaps := ((List.finRange 15).flatMap fun x =>
  ((List.finRange 15).filter (fun y => x<y && decide (¬(side x ↔ side y)))).map (x,·))

private def losses (xy : Fin 15 × Fin 15) :=
  (List.finRange 15).filter (fun c => loses (layoutEdges pivotColoring (swapPoints xy.1 xy.2 fifteen) c))
private def lossSets := repairingSwaps.map losses

/-- Each choice of twelve previously connected colors can be preserved
while repairing the last color. Two choices of thirteen block every swap:
protect all the old colors except 3, or protect all except 4. -/
theorem protection_table :
    (∀ u v : Fin 15,u≠8 → v≠8 → u≠v → lossSets.any (fun row => row.all (fun c => c==u || c==v))=true) ∧
    (∀ u : Fin 15,u≠8 → (lossSets.any (fun row => row.all (fun c => c==u))=true ↔ u≠3 ∧ u≠4)) := by native_decide

def finished := [[1,2,4],[3,8,13],[5,6,11],[0,9,10],[7,12,14]]

theorem example_exact : Exact pivotColoring 10 := by
  let w : Lines 15 := (chains finished).toFinset
  have legal : Legal w := by unfold Legal; native_decide
  have size : w.card=10 := by native_decide
  exact ⟨⟨w,legal,size,works_of_layout pivotColoring finished (by native_decide)⟩,fun _ h p => odd_lower (by decide) pivotColoring h p⟩

#print axioms protection_table
#print axioms checked_rows
#print axioms exactly_two
#print axioms swap_trap
#print axioms example_exact
end WildExact.Regroup.SwitchCases
