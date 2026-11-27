import TwoCoreCheck
namespace WildCuts.OneExtra.Trap21
open Finset WildExact EdgeWalk
private def rows : Array (Array (Fin 21)) := #[
  #[0,13,4,11,9,5,0,2,7,1,6,8,17,3,19,18,20,16,10,15,12],
  #[13,0,2,5,7,14,9,3,11,4,17,1,10,19,15,0,12,6,16,18,8],
  #[4,2,0,14,19,15,11,17,0,9,8,3,12,16,6,13,5,1,18,10,20],
  #[11,5,14,0,6,20,18,0,12,8,1,15,13,10,7,19,9,17,4,2,16],
  #[9,7,19,6,0,1,13,10,20,2,5,4,0,11,14,15,3,12,17,8,18],
  #[5,14,15,20,1,0,6,16,8,17,0,18,11,4,13,3,19,7,2,9,10],
  #[0,9,11,18,13,6,0,19,5,12,7,20,4,14,1,16,8,10,15,3,2],
  #[2,3,17,0,10,16,19,0,13,11,15,9,20,7,12,6,4,18,14,1,5],
  #[7,11,0,12,20,8,5,13,0,10,2,14,3,15,16,4,17,9,1,19,6],
  #[1,4,9,8,2,17,12,11,10,0,3,6,16,18,5,20,15,19,13,14,7],
  #[6,17,8,1,5,0,7,15,2,3,0,16,9,12,4,10,18,14,20,13,19],
  #[8,1,3,15,4,18,20,9,14,6,16,0,19,13,17,2,7,0,12,5,11],
  #[17,10,12,13,0,11,4,20,3,16,9,19,0,1,18,7,14,2,8,6,15],
  #[3,19,16,10,11,4,14,7,15,18,12,13,1,0,8,17,2,5,6,20,0],
  #[19,15,6,7,14,13,1,12,16,5,4,17,18,8,0,9,10,20,11,0,3],
  #[18,0,13,19,15,3,16,6,4,20,10,2,7,17,9,0,11,8,5,12,14],
  #[20,12,5,9,3,19,8,4,17,15,18,7,14,2,10,11,0,13,0,16,1],
  #[16,6,1,17,12,7,10,18,9,19,14,0,2,5,20,8,13,0,3,11,4],
  #[10,16,18,4,17,2,15,14,1,13,20,12,8,6,11,5,0,3,0,7,9],
  #[15,18,10,2,8,9,3,1,19,14,13,5,6,20,0,12,16,11,7,0,17],
  #[12,8,20,16,18,10,2,5,6,7,19,11,15,0,3,14,1,4,9,17,0]]
private def paint (x y : Fin 21) := rows[x.val]![y.val]!
def graph : Coloring 21 21 where
  paint := paint
  symm := by native_decide
  proper := by native_decide
def certificates : List (Fin 21 × Nat) := [
  (0,461),(1,3595),(6,3609),(7,22),(9,262094),(10,262106),(13,467),(13,229383),
  (14,2097116),(20,2097109)]
def exterior := CoreTest.exteriorEdges 21 6
def repaired := CoreTest.redraw 21 6 7 0 6
set_option maxRecDepth 20000
set_option maxHeartbeats 0
theorem reaches : MeetsCore graph exterior.toFinset (CoreTest.first 21 6) :=
  CoreTest.reaches graph exterior _ (by native_decide)

theorem no_split (A : Finset (Fin 21)) (hA : A∈CoreTest.splits 21 6) (w : Lines 21)
    (within : ∀ e∈w,e∈exterior ∨ (e.1∈A ∧ e.2∈A) ∨
      (e.1∈CoreTest.first 21 6 \ A ∧ e.2∈CoreTest.first 21 6 \ A)) : ¬Works graph w :=
  CoreTest.no_split graph exterior (CoreTest.first 21 6) certificates
    (checked:=(by native_decide)) (all:=(by native_decide)) A hA w within

/-- Swapping core vertex 0 with exterior vertex 6 makes a target-size redraw possible. -/
theorem repaired_exact : Exact graph 14 :=
  CoreTest.winner graph (by decide) repaired (by native_decide) (by native_decide) (by native_decide)

theorem split_count : (CoreTest.splits 21 6).card=20 := by native_decide
#print axioms no_split
#print axioms repaired_exact
end WildCuts.OneExtra.Trap21
