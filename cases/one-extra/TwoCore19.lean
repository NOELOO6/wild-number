import TwoCoreCheck
namespace WildCuts.OneExtra.Trap19
open Finset WildExact EdgeWalk
private def rows : Array (Array (Fin 19)) := #[
  #[0,8,13,17,5,12,10,2,1,16,11,14,9,7,3,18,4,6,15],
  #[8,0,0,15,6,3,11,1,4,13,5,10,14,2,7,17,18,12,9],
  #[13,0,0,3,15,18,5,9,10,17,14,8,6,16,4,1,11,2,7],
  #[17,15,3,0,0,1,14,11,18,8,9,7,4,10,5,2,6,16,12],
  #[5,6,15,0,0,2,17,18,13,3,1,11,7,12,9,16,8,4,10],
  #[12,3,18,1,2,0,13,7,11,15,4,9,16,6,14,8,10,5,0],
  #[10,11,5,14,17,13,0,4,7,6,0,15,8,18,16,12,1,9,2],
  #[2,1,9,11,18,7,4,0,3,10,13,17,0,8,6,14,12,15,16],
  #[1,4,10,18,13,11,7,3,0,9,16,12,2,14,17,0,15,8,5],
  #[16,13,17,8,3,15,6,10,9,0,2,18,12,4,1,11,5,0,14],
  #[11,5,14,9,1,4,0,13,16,2,0,6,10,15,12,3,7,18,17],
  #[14,10,8,7,11,9,15,17,12,18,6,0,5,0,2,4,16,3,13],
  #[9,14,6,4,7,16,8,0,2,12,10,5,0,3,15,13,17,1,18],
  #[7,2,16,10,12,6,18,8,14,4,15,0,3,0,11,5,13,17,1],
  #[3,7,4,5,9,14,16,6,17,1,12,2,15,11,0,10,0,13,8],
  #[18,17,1,2,16,8,12,14,0,11,3,4,13,5,10,0,9,7,6],
  #[4,18,11,6,8,10,1,12,15,5,7,16,17,13,0,9,0,14,3],
  #[6,12,2,16,4,5,9,15,8,0,18,3,1,17,13,7,14,0,11],
  #[15,9,7,12,10,0,2,16,5,14,17,13,18,1,8,6,3,11,0]]
private def paint (x y : Fin 19) := rows[x.val]![y.val]!
def graph : Coloring 19 19 where
  paint := paint
  symm := by native_decide
  proper := by native_decide
def certificates : List (Fin 19 × Nat) := [
  (0,7),(0,25),(0,30),(2,65419),(3,46),(3,924),(3,946),(3,523277),
  (3,523299),(3,524189),(3,524211),(5,7187),(5,64539),(5,459697),(5,517049),(5,524202),
  (6,7190),(8,517048),(9,7209),(9,8109),(10,65422),(10,459700),(10,466870),(10,517052),
  (10,523322),(11,465941),(11,517036),(12,37),(13,524183),(13,524186),(14,524199),(15,459691),
  (15,459701),(17,524175),(17,524198)]
def exterior := CoreTest.exteriorEdges 19 7
def repaired := CoreTest.redraw 19 7 7 0 7
set_option maxRecDepth 20000
set_option maxHeartbeats 0
theorem reaches : MeetsCore graph exterior.toFinset (CoreTest.first 19 7) :=
  CoreTest.reaches graph exterior _ (by native_decide)

theorem no_split (A : Finset (Fin 19)) (hA : A∈CoreTest.splits 19 7) (w : Lines 19)
    (within : ∀ e∈w,e∈exterior ∨ (e.1∈A ∧ e.2∈A) ∨
      (e.1∈CoreTest.first 19 7 \ A ∧ e.2∈CoreTest.first 19 7 \ A)) : ¬Works graph w :=
  CoreTest.no_split graph exterior (CoreTest.first 19 7) certificates
    (checked:=(by native_decide)) (all:=(by native_decide)) A hA w within

/-- Swapping core vertex 0 with exterior vertex 7 makes a target-size redraw possible. -/
theorem repaired_exact : Exact graph 13 :=
  CoreTest.winner graph (by decide) repaired (by native_decide) (by native_decide) (by native_decide)

theorem split_count : (CoreTest.splits 19 7).card=70 := by native_decide
#print axioms no_split
#print axioms repaired_exact
end WildCuts.OneExtra.Trap19
