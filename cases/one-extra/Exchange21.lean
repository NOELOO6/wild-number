import Exchange21Data
import CoreBudget
namespace WildCuts.OneExtra.Exchange21
open Finset WildExact WildDeletion

abbrev Exchange := Option {e : Fin 21 × Fin 21 // e.1<e.2}
def core := CoreTest.first 21 6
def layouts := choices core (0 : Fin 21)
def index : Exchange → Nat
  | none => 210
  | some e =>
    let a := e.val.1.val
    a*(41-a)/2+e.val.2.val-a-1

def perm : Exchange → Equiv.Perm (Fin 21)
  | none => Equiv.refl _
  | some e => Equiv.swap e.val.1 e.val.2

def label (m : Exchange) (A : Finset (Fin 21)) (x : Fin 21) :=
  let v := (perm m).symm x
  if v.val<6 then (if v∈A then 0 else 1) else 2+(v.val-6)/3

set_option maxRecDepth 20000
set_option maxHeartbeats 0
private def row (m : Exchange) := cutRows[index m]!
private theorem closedCuts : ∀ m,∀ j∈row m,let S := CoreTest.points 21 j.2
    S.Nonempty ∧ (∃ x : Fin 21,x∉S) ∧
    ∀ x y : Fin 21,x≠y → graph.paint x y=j.1 → (x∈S ↔ y∈S) := by native_decide

private theorem witnesses : ∀ m : Exchange,∀ A : ↥layouts,∃ j∈row m,∀ x y : Fin 21,
    label m A.val x=label m A.val y → (x∈CoreTest.points 21 j.2 ↔ y∈CoreTest.points 21 j.2) := by native_decide

theorem reaches : MeetsCore graph (CoreTest.exteriorEdges 21 6).toFinset core :=
  CoreTest.reaches graph _ _ (by native_decide)

theorem counts : Fintype.card Exchange=211 ∧ layouts.card=10 := by native_decide

/-- Any single transposition of the 21 vertices, followed by any of the ten
core splits, preserves an explicit cut. The case without a transposition
is included. The conclusion allows arbitrary wild edges within the groups. -/
theorem no_one_exchange (m : Exchange) (A : Finset (Fin 21)) (ha : A∈layouts)
    (w : Lines 21) (inside : ∀ e∈w,label m A e.1=label m A e.2) : ¬Works graph w := by
  obtain ⟨j,hj,whole⟩ := witnesses m ⟨A,ha⟩
  obtain ⟨⟨x,hx⟩,⟨y,hy⟩,closed⟩ := closedCuts m j hj
  let S := CoreTest.points 21 j.2
  have stays {u v : Fin 21} (h : Walk (Joined graph w j.1) u v) : u∈S → v∈S := by
    induction h with
    | stay => exact id
    | step _ edge ih =>
      rcases edge with (e|e)|⟨ne,col⟩
      · exact fun hu => (whole _ _ (inside _ e)).mp (ih hu)
      · exact fun hu => (whole _ _ (inside _ e)).mpr (ih hu)
      · exact fun hu => (closed _ _ ne col).mp (ih hu)
  exact fun wins => hy (stays (wins j.1 x y) hx)

def twoChanges : List (EdgeWalk.Edge 21) :=
  let p := Equiv.swap (1 : Fin 21) 10
  (CoreTest.redraw 21 6 52 0 6).map (fun e => (min (p e.1) (p e.2),max (p e.1) (p e.2)))

/-- Two exchanges suffice. Exchange 0 with 6 and 1 with 10. -/
theorem repairs : Exact graph 14 ∧ Works graph twoChanges.toFinset := by
  have a : ∀ c,EdgeWalk.passes 0 (twoChanges++CoreTest.colored graph c)=true := by native_decide
  exact ⟨CoreTest.winner graph (by decide) twoChanges (by native_decide) (by native_decide) a,
    fun c x y => CoreTest.to_graph graph _ c (EdgeWalk.connected_of_passes 0 _ (a c) x y)⟩

#print axioms no_one_exchange
#print axioms repairs
end WildCuts.OneExtra.Exchange21
