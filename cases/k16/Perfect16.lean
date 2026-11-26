import Std

/- Gill and Wanless supply the classified representatives. Each line of our
   witness file has one partition for each possible deleted point, in order.
   Search used a union-find on the five groups. Lean uses separating cuts. -/
namespace Perfect16
set_option maxRecDepth 300000
set_option maxHeartbeats 0

abbrev Matching := List (Nat × Nat)
abbrev Coloring := List Matching
def words' (line : String) := (line.splitOn " ").filter (fun t => !t.isEmpty)
def lines' (doc : String) := (doc.splitOn "\n").filter (fun t => !t.isEmpty)
def letters (s : String) := s.toList.map (fun c => if 'a' ≤ c ∧ c ≤ 'p' then c.toNat - 'a'.toNat else 16)
def toEdges : List Nat → Matching
  | a::b::rest => (a,b) :: toEdges rest
  | [] => []
  | [a] => [(a,a)]

def data : List Coloring := (lines' (include_str "P1F16catalogue")).map fun line =>
  (words' line).map (fun w => toEdges (letters w))
def witnesses := (lines' (include_str "P1F16witnesses")).map
  (fun line => (words' line).map letters)
def rows := data.zip witnesses

def genuineMatching (m : Matching) := m.length == 8 &&
  (List.range 16).all (fun x => m.any (fun (a,b) => a == x || b == x))
def proper (f : Coloring) := f.length == 15 && f.all genuineMatching &&
  ((List.range 16).all fun a => (List.range a).all fun b =>
    f.any (fun m => m.any (fun (u,v) => (u == a && v == b) || (v == a && u == b))))

def tripleMasks : List Nat → List Nat
  | a::b::c::rest => ((1 <<< a) ||| (1 <<< b) ||| (1 <<< c)) :: tripleMasks rest
  | _ => []

def side (gs : List Nat) (mask : Nat) :=
  gs.zipIdx.foldl (fun u (g,i) => if mask.testBit i then u ||| g else u) 0

def genuine (r : Nat) (p : List Nat) := p.length == 15 &&
  (List.range 16).all (fun v => v == r || p.contains v) && !p.contains r

/-- On the remaining 15 points, every bipartition of the five connected
    triples must have an edge of the selected color crossing it. Complementary
    cuts have the same crossing edges, so masks 1 through 15 suffice. -/
def connectedGroups (f : Coloring) (r : Nat) (p : List Nat) :=
  let gs := tripleMasks p
  let sides := (List.range' 1 15).map (side gs)
  f.all fun m => sides.all fun s =>
    m.any fun (a,b) => a != r && b != r && (s.testBit a != s.testBit b)

def works (f : Coloring) (r : Nat) (p : List Nat) := genuine r p && connectedGroups f r p

theorem number_representatives : data.length = 3155 := by native_decide
theorem complete_file : rows.map Prod.fst = data := by native_decide
theorem accepted : rows.all (fun (f, ws) => proper f &&
    (List.range 16).all (fun r => works f r (ws[r]?.getD []))) = true := by native_decide

theorem every_representative_every_deletion (f : Coloring) (listed : f ∈ data) (r : Fin 16) :
    proper f = true ∧ ∃ p, genuine r.val p = true ∧ connectedGroups f r.val p = true := by
  rw [← complete_file] at listed
  obtain ⟨⟨f',ws⟩, hrow, he⟩ := List.mem_map.mp listed
  change f' = f at he
  subst f'
  have hh := Bool.and_eq_true_iff.mp (List.all_eq_true.mp accepted (f,ws) hrow)
  have good := List.all_eq_true.mp hh.2 r.val (List.mem_range.mpr r.isLt)
  exact ⟨hh.1, ws[r.val]?.getD [], Bool.and_eq_true_iff.mp good⟩

#print axioms every_representative_every_deletion
end Perfect16
