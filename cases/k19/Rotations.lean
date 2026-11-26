import EdgeWalk
namespace K19Rotation
open EdgeWalk WildDeletion
abbrev V := Fin 19
abbrev Edges := List (Edge 19)
def points := List.finRange 19
def distance (a b : V) := min (b.val-a.val) (19-(b.val-a.val))

/-- A matching on the listed points, with no repeated circular distances.
The least remaining point is written first in its edge. -/
inductive Starter : List V → List Nat → Edges → Prop where
  | empty (used) : Starter [] used []
  | pair {a b rest used tail} (present : b ∈ rest) (fresh : distance a b ∉ used)
      (next : Starter (rest.erase b) (distance a b :: used) tail) :
      Starter (a::rest) used ((a,b)::tail)

def generate : Nat → List V → List Nat → List Edges
  | _, [], _ => [[]]
  | 0, _::_, _ => []
  | fuel+1, a::rest, used => rest.flatMap fun b =>
    if distance a b ∈ used then [] else
      (generate fuel (rest.erase b) (distance a b :: used)).map ((a,b) :: ·)

theorem exhaustive {xs used es} (h : Starter xs used es) (fuel : Nat)
    (enough : es.length ≤ fuel) : es ∈ generate fuel xs used := by
  induction h generalizing fuel with
  | empty => cases fuel <;> simp [generate]
  | @pair a b rest used tail hb hf _ ih =>
    cases fuel with
    | zero => simp at enough
    | succ k =>
      simp only [generate, List.mem_flatMap]
      exact ⟨b, hb, by simp [hf, List.mem_map, ih k (by simpa using enough)]⟩

def starters := generate 9 points.tail []
def rot (c v : V) : V := ⟨(v.val+c.val)%19, Nat.mod_lt _ (by decide)⟩
def shifted (s : Edges) (c : V) : Edges := s.map fun (a,b) => (rot c a,rot c b)

def chain : List V → Edges
  | a::b::rest => (a,b) :: chain (b::rest)
  | _ => []
def layout (labels : List Nat) : Edges := (List.range 6).flatMap fun k =>
  chain (points.filter fun v => labels[v.val]? == some k)
def layouts := (((include_str "layouts.txt").splitOn "\n").filter (· != "")).map fun line =>
  layout ((line.splitOn " ").map String.toNat!)
def choices := (include_str "choices.txt").trim.toList.map fun c => c.toNat - 33
def rows := starters.zip choices
def works (s w : Edges) := w.length == 13 && points.all fun c => passes 0 (w ++ shifted s c)
def rowOK (p : Edges × Nat) := works p.1 (layouts[p.2]?.getD [])
def completeGraphEdges := (List.range 19).flatMap fun b => (List.range b).map (fun a => 19*b+a)
def properColoring (s : Edges) :=
  let ms := points.map (shifted s)
  (ms.all fun m => let vs := m.flatMap (fun (a,b) => [a,b])
                   m.length == 9 && vs.eraseDups.length == 18) &&
    ((ms.flatten.map fun (a,b) => 19*(max a.val b.val)+min a.val b.val).mergeSort (· ≤ ·)) == completeGraphEdges
end K19Rotation
