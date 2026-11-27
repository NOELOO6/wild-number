import SwapExamples
import Lean.Data.Json.Parser
import Lean.Data.Json.FromToJson

namespace WildExact.Regroup.QuartetTrap
open WildDeletion EdgeWalk
set_option maxRecDepth 10000

private def rows : Array (Array Nat) :=
  let data := do
    let obj ← Lean.Json.parse (include_str "coloring.json")
    Lean.fromJson? (← obj.getObjVal? "mates")
  data.toOption.getD #[]

def partner (c : Fin 15) (v : Fin 16) : Fin 16 := Fin.ofNat' 16 ((rows[c.val]!)[v.val]!)
private def paint (x y : Fin 16) : Fin 15 :=
  Fin.ofNat' 15 (rows.findIdx (fun row => row[x.val]! == y.val))

def coloring : Coloring 16 15 where
  paint := paint
  symm := by native_decide
  proper := by native_decide

private theorem partner_of_edge : ∀ x y : Fin 16, x≠y → partner (coloring.paint x y) x=y := by native_decide

def quartets : List (List Nat) := [[0,1,2,3],[4,5,6,7],[8,9,10,11],[12,13,14,15]]

theorem coarse_works : Works coloring (chains quartets).toFinset :=
  works_of_layout coloring quartets (by native_decide)

/-- All six internal edges of each starting quartet have distinct colors. -/
theorem coarse_rainbow : ∀ x y u v : Fin 16,
    x<y → u<v → x.val/4=y.val/4 → x.val/4=u.val/4 → x.val/4=v.val/4 →
    coloring.paint x y=coloring.paint u v → (x,y)=(u,v) := by native_decide

/-- Select the point with index a,b,c,d, respectively, from each quartet.
Three of those points become a new triple. The point picked from quartet r
stands alone. The four old quartets each retain three points. -/
def cell (a b c d r : Fin 4) (v : Fin 16) : Nat :=
  let q := v.val/4
  let picked := if q=0 then a else if q=1 then b else if q=2 then c else d
  if v.val%4=picked.val then (if q=r.val then 5 else 4) else q

private def side (m : Fin 31) (q : Nat) := (m.val+1).testBit q

private theorem witnesses : ∀ a b c d r : Fin 4, ∃ k : Fin 15, ∃ m : Fin 31,
    (∀ v : Fin 16,side m (cell a b c d r v)=side m (cell a b c d r (partner k v))) ∧
    ∃ x y : Fin 16,side m (cell a b c d r x)≠side m (cell a b c d r y) := by native_decide

/-- All 4^5 redraws fail. Each cut certificate also excludes any other wild
edges entirely contained in the same six groups. -/
theorem every_redraw_fails (a b c d r : Fin 4) : ∃ k : Fin 15,∀ w : Lines 16,
    (∀ e∈w,cell a b c d r e.1=cell a b c d r e.2) → ¬ Connected (Joined coloring w k) := by
  obtain ⟨k,m,closed,x,y,diff⟩ := witnesses a b c d r
  refine ⟨k,fun w grouped conn => diff ?_⟩
  have same {u v : Fin 16} (walk : Walk (Joined coloring w k) u v) :
      side m (cell a b c d r u)=side m (cell a b c d r v) := by
    induction walk with
    | stay => rfl
    | step _ e ih =>
      apply ih.trans
      rcases e with (h|h)|⟨ne,col⟩
      · exact congrArg (side m) (grouped _ h)
      · exact (congrArg (side m) (grouped _ h)).symm
      · have eq := partner_of_edge _ _ ne
        rw [col] at eq
        exact (closed _).trans (congrArg (fun v => side m (cell a b c d r v)) eq)
  exact same (conn x y)

def solution : List (List Nat) := [[0,1,2],[3,4,5],[6,7,9],[8,10,14],[11,12,13]]

theorem ten_work : Upper coloring 10 := by
  refine ⟨(chains solution).toFinset,?_,?_,works_of_layout coloring solution (by native_decide)⟩
  · unfold Legal
    native_decide
  · decide

#print axioms every_redraw_fails
#print axioms ten_work
end WildExact.Regroup.QuartetTrap
