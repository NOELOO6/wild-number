import ExteriorSound
import SixTrap
namespace WorkedStar
open VertexRedraw ExteriorRows EdgeWalk WildDeletion
def missing : List Nat := [10,0,11,8,2,1,4,7,12]
def chosen (c : C) := (missing.idxOf? c.val).map (·+1) |>.getD 0
def rows := (numbers (include_str "one-outside-change.txt")).map List.toArray
def mate (c : C) (x : V) : V := Fin.ofNat' 16 rows[c.val]![x.val]!
def endID : Fin 280 := 106
theorem checked : properRows rows=true ∧ (∀ c : C, key (mate c 15)=chosen c) ∧
    (∀ c x, BoundaryOptions.fixedAt lock c x=true → mate c x=SixBoundary.ref c x) ∧
    FixedSix.endings[endID.val]?=some [2240,12544,17920] ∧
    budget chosen endID=9 := by native_decide

theorem original_cheapest : (ends.map (fun j =>
    budget (fun c => key (SixBoundary.ref c 15)) j)).min? = some 10 := by native_decide

theorem all_completions (f : C→V→V) (inv : ∀ c x, f c (f c x)=x) (ne : ∀ c x, f c x≠x)
    (proper : ∀ c d, c≠d → ∀ x, f c x≠f d x)
    (agree : ∀ c x, BoundaryOptions.fixedAt lock c x=true → f c x=SixBoundary.ref c x)
    (star : ∀ c, key (f c 15)=chosen c) :
    ∃ g ∈ FixedSix.all, (trial g).length=10 ∧ (trial g).Nodup ∧
      ∀ c, Connected (Adj (trial g++actualEdges (f c))) := by
  apply price_winner f inv ne proper agree endID
  simp only [star,checked.2.2.2.2]
  decide
end WorkedStar
