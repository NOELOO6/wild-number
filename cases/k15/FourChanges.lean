import Std

/- A fixed, proper coloring on fifteen vertices. Any extension of any
   seven original edges by at most three lines leaves a color disconnected.
   The proof searches cuts. It imposes no shape restriction on the additions. -/
namespace FourChanges
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def mates : Array (Array Nat) := #[#[3,2,1,0,15,6,5,14,10,11,8,9,13,12,7,4],#[2,5,0,7,9,1,12,3,14,4,11,10,6,15,8,13],#[4,15,3,2,0,7,9,5,12,6,13,14,8,10,11,1],#[12,9,11,4,3,14,13,10,15,1,7,2,0,6,5,8],#[14,4,6,11,1,12,2,13,9,8,15,3,5,7,0,10],#[13,3,14,1,10,9,8,11,6,5,4,7,15,0,2,12],#[6,14,9,15,5,4,0,8,7,2,12,13,10,11,1,3],#[1,0,10,9,12,13,14,15,11,3,2,8,4,5,6,7],#[9,10,4,13,2,8,7,6,5,0,1,15,14,3,12,11],#[5,13,12,8,7,0,11,4,3,10,9,6,2,1,15,14],#[15,12,8,14,13,11,10,9,2,7,6,5,1,4,3,0],#[8,7,5,10,11,2,15,1,0,12,3,4,9,14,13,6],#[11,6,7,12,8,15,1,2,4,13,14,0,3,9,10,5],#[7,8,13,6,14,10,3,0,1,15,5,12,11,2,4,9],#[10,11,15,5,6,3,4,12,13,14,0,1,7,8,9,2]]
def oldEdges : List (Nat × Nat) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(9,10),(10,11),(12,13),(13,14)]
def newEdges : List (Nat × Nat) := [(0,1),(1,2),(3,4),(3,6),(5,8),(5,9),(10,11),(7,10),(12,13),(13,14)]

def index (a b : Nat) := let h := max a b; h*(h-1)/2 + min a b
def allEdges := (List.range 15).flatMap fun b => (List.range b).map (fun a => (a,b))
def indices (es : List (Nat × Nat)) := es.map (fun (a,b) => index a b)
def original := indices oldEdges
def solution := indices newEdges
def crossings (s : Nat) := allEdges.foldl (fun m (a,b) =>
  if s.testBit a != s.testBit b then m ||| (1 <<< index a b) else m) 0
def colorMask (c : Nat) := (List.range 15).foldl (fun m x =>
  let y := mates[c]![x]!
  if x < y && y < 15 then m ||| (1 <<< index x y) else m) 0
def colors := (List.range 15).map colorMask
def weight (s : Nat) := ((List.range 15).filter s.testBit).length
def sides := (List.range' 1 32766).mergeSort (fun a b => weight a ≤ weight b)

/-- For each nontrivial vertex cut that at least one color cannot cross,
    the wild edges must hit its crossing-edge mask. -/
def demands := sides.filterMap fun s =>
  let q := crossings s
  if colors.any (fun c => (c &&& q) == 0) then some q else none
def Hits (qs es : List Nat) : Prop := ∀ q ∈ qs, ∃ e ∈ es, q.testBit e = true
def Works (es : List Nat) := Hits demands es
def waiting (qs es : List Nat) := qs.filter (fun q => !(es.any q.testBit))
def kept (selector : Nat) := (original.zipIdx.filter (fun (_,i) => selector.testBit i)).map Prod.fst

/-- Branch on a line required by the first outstanding cut. -/
def impossible : Nat → List Nat → Bool
  | 0, qs => !qs.isEmpty
  | _+1, [] => false
  | k+1, q::qs => (List.range 105).all (fun e => !q.testBit e ||
      impossible k (qs.filter (fun d => !d.testBit e)))

theorem sound (k : Nat) (qs es : List Nat) (proof : impossible k qs = true)
    (valid : ∀ e ∈ es, e < 105) (bound : es.length ≤ k) : ¬Hits qs es := by
  intro allHit
  induction k generalizing qs es with
  | zero =>
    have hnil : es = [] := List.length_eq_zero_iff.mp (by omega)
    subst es
    cases qs with
    | nil => contradiction
    | cons q qs =>
      obtain ⟨e,he,_⟩ := allHit q (by simp)
      simp at he
  | succ k ih =>
    cases qs with
    | nil => contradiction
    | cons q qs =>
      obtain ⟨e,he,hit⟩ := allHit q (by simp)
      have branch := List.all_eq_true.mp proof e (List.mem_range.mpr (valid e he))
      simp [hit] at branch
      apply ih _ (es.erase e) branch
      · intro i hi; exact valid i (List.mem_of_mem_erase hi)
      · have len := List.length_erase_of_mem he
        have pos := List.length_pos_of_mem he
        omega
      · intro d hd
        obtain ⟨hd,hmiss⟩ := List.mem_filter.mp hd
        obtain ⟨i,hi,yes⟩ := allHit d (by simp [hd])
        have ne : i ≠ e := by intro eq; subst i; simp [yes] at hmiss
        exact ⟨i, (List.mem_erase_of_ne ne).mpr hi, yes⟩

theorem finite_check : (List.range 1024).all (fun m =>
    (kept m).length != 7 || impossible 3 (waiting demands (kept m))) = true := by native_decide

theorem no_three_changes (m : Fin 1024) (seven : (kept m.val).length = 7)
    (added : List Nat) (valid : ∀ e ∈ added, e < 105) (short : added.length ≤ 3) :
    ¬Works (kept m.val ++ added) := by
  intro h
  have checked := List.all_eq_true.mp finite_check m.val (List.mem_range.mpr m.isLt)
  simp [seven] at checked
  apply sound 3 _ added checked valid short
  intro q hq
  obtain ⟨hd,hn⟩ := List.mem_filter.mp hq
  obtain ⟨e,he,hit⟩ := h q hd
  rcases List.mem_append.mp he with ho | ha
  · have hh := List.any_eq_true.mpr ⟨e,ho,hit⟩
    simp [hh] at hn
  · exact ⟨e,ha,hit⟩

theorem solution_works : Works solution := by
  have h : demands.all (fun q => solution.any q.testBit) = true := by native_decide
  exact fun q hq => List.any_eq_true.mp (List.all_eq_true.mp h q hq)
theorem four_replaced :
    original.Nodup ∧ solution.Nodup ∧ original.length = 10 ∧ solution.length = 10 ∧
    (original.filter solution.contains).length = 6 := by native_decide

theorem proper : mates.size = 15 ∧ (∀ c : Fin 15, mates[c.val]!.size = 16) ∧
    (∀ (c : Fin 15) (x : Fin 16), let y := mates[c.val]![x.val]!
       y < 16 ∧ y ≠ x.val ∧ mates[c.val]![y]! = x.val) ∧
    (∀ x y : Fin 16, x ≠ y → ((List.range 15).filter (fun c => mates[c]![x.val]! == y.val)).length = 1) := by native_decide

def oldMask := original.foldl (fun z e => z ||| (1 <<< e)) 0
def connectedColor (c : Nat) := sides.all fun s => ((oldMask ||| colorMask c) &&& crossings s) != 0
theorem one_color_fails : ((List.range 15).filter (fun c => !connectedColor c)) = [6] := by native_decide

/-- An alternating square through a vertex is detected by four alternating
    partner steps. Its count is invariant under any symmetry of the coloring. -/
def squares (v : Nat) := ((List.range 15).flatMap (fun c =>
  (List.range c).filter (fun d => mates[c]![mates[d]![mates[c]![mates[d]![v]!]!]!]! == v))).length
theorem different_square_counts : squares 0 = 12 ∧ squares 2 = 8 := by native_decide
def pure (s : Nat) (m : Array Nat) :=
  let vs := List.range 16
  vs.all (fun x => s.testBit x == s.testBit m[x]!) ||
  vs.all (fun x => s.testBit x != s.testBit m[x]!)
theorem no_two_teams : (List.range 32768).all (fun s =>
    weight s != 8 || !mates.all (pure s)) = true := by native_decide

#print axioms no_three_changes
#print axioms solution_works
end FourChanges
