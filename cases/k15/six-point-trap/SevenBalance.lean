import SevenProfile

namespace SevenProfile
open VertexRedraw ThreeStars EdgeWalk

def rootEdges : R := (points.filter (fun x => x.val < 6)).map (·,15)
def sixEdges : R := points.flatMap fun x => points.filterMap fun y =>
  if x < y ∧ y.val < 6 then some (x,y) else none
def same (e : Edge 16) := decide (e.1.val<3) == decide (e.2.val<3)
def withinEdges := sixEdges.filter same
def acrossEdges := sixEdges.filter (fun e => !same e)
def hits (m : R) (e : Edge 16) := m.contains e || m.contains (e.2,e.1)
def tally (m es : R) := Teams.total es (fun e => if hits m e then 1 else 0)
def accounting (m : R) := decide (
    tally m rootEdges = count 32831 m-count 63 m ∧
    tally m withinEdges = count 7 m+count 56 m ∧
    tally m acrossEdges = count 63 m-(count 7 m+count 56 m) ∧
    count 7 m+count 56 m ≤ count 63 m ∧ count 63 m ≤ count 32831 m ∧
    count 32831 m-count 63 m ≤ 1)

end SevenProfile
