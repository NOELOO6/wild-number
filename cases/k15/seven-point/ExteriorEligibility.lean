import ExteriorStars
namespace ExteriorRows
open VertexRedraw

/-- Count the endpoints on the two sides of a perfect matching. -/
theorem edge_difference (inside outside crossing : Nat)
    (seven : 2*inside+crossing=7) (nine : 2*outside+crossing=9) :
    outside=inside+1 := by omega

def eligibleColor (c : C) (m : R) :=
  let x := root m
  let onSeven (p : V) := p.val<6 || p.val==15
  decide ((m.filter (fun e => onSeven e.1 && onSeven e.2)).length ≤ 2) &&
    (oldCount c != 1 || outside x) && (!outside x || (pricesAt x).contains c)

theorem eligibility_checked : required=[0,7,11,12] ∧
    colors.all (fun c => opts[c.val]!.all (eligibleColor c))=true := by native_decide
end ExteriorRows
