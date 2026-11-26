import CrossBoundary
namespace Replacement
open VertexRedraw EdgeWalk WildDeletion
open SixBoundary (ref)
def splitOnly := (numbers (include_str "two-originals-left.txt")).map List.toArray
def replaceAll := (numbers (include_str "replace-the-nineteen.txt")).map List.toArray
def partner (rs : List (Array Nat)) (c : C) (x : V) := Fin.ofNat' 16 rs[c.val]![x.val]!
def ordinary (rs : List (Array Nat)) := rs.map fun m => actualEdges (fun v => Fin.ofNat' 16 m[v.val]!)
def changed (rs : List (Array Nat)) := colors.flatMap fun c => points.filterMap fun x =>
  let y := ref c x
  if x<y && y.val<15 && partner rs c x != y then some (x.val,y.val) else none
def verify (rs : List (Array Nat)) (wins kept : Nat) :=
  let cs := ordinary rs
  let w := FixedSix.all.filter (fun g => SixTrap.classify (trial g) cs == .win)
  decide (w.length=wins ∧ (w.filter FixedSix.succeeds).length=kept ∧
    (FixedSix.all.filter (fun g => SixTrap.classify (trial g) cs == .loss)).length=2800-wins)

theorem crossing_example : properRows splitOnly=true ∧
    (∀ c x, CrossBoundary.fixedAt c x=true → partner splitOnly c x=ref c x) ∧
    (changed splitOnly).length=31 ∧ verify splitOnly 36 2=true := by native_decide

theorem inside_swap : properRows replaceAll=true ∧
    (∀ c x, (x.val==15 || (ref c x).val==15 || (6≤x.val && 6≤(ref c x).val))=true →
      partner replaceAll c x=ref c x) ∧
    replaceAll.all (fun m => SixTrap.edgesInside FixedSix.seven m≤2)=true ∧
    (changed replaceAll).length=36 ∧
    ((changed replaceAll).filter (fun e => e.2<6))=[(1,2),(1,4)] ∧
    verify replaceAll 43 0=true := by native_decide
end Replacement
