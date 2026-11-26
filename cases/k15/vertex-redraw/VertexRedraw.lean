import EdgeWalk
import WeightedSurvivor

namespace VertexRedraw
open EdgeWalk WildDeletion
abbrev V := Fin 16
abbrev C := Fin 15
abbrev R := List (Edge 16)
abbrev E := List (Edge 15)

def points := List.finRange 16
def colors := List.finRange 15
private theorem point_mem : ∀ x : V, x ∈ points := by decide
def numbers (s : String) := (s.trim.splitOn "\n").map fun line =>
  (line.splitOn " ").filterMap String.toNat?
def referenceRows := ((numbers (include_str "example.txt")).map List.toArray).toArray
def partner (c : C) (v : V) : V := Fin.ofNat' 16 referenceRows[c.val]![v.val]!
def centers : List V := [0,1,3,8,15]
def known (c : C) (v : V) := centers.contains v || centers.contains (partner c v)
def fixed (c : C) : R := points.filterMap fun x =>
  if known c x && decide (x < partner c x) then some (x,partner c x) else none
def free (c : C) := points.filter fun x => !known c x
def erase (m : R) : E := m.filterMap fun (x,y) =>
  if h : x.val < 15 ∧ y.val < 15 then some (⟨x.val,h.1⟩,⟨y.val,h.2⟩) else none

/-- Pair the first free vertex with each possible partner among the others. -/
def fills : Nat → List V → List R
  | _, [] => [[]]
  | 0, _::_ => []
  | d+1, x::xs => xs.flatMap fun y =>
      (fills d (xs.filter fun z => z != x && z != y)).map ((x,y) :: ·)

def respects (f : V → V) (m : R) := ∀ e ∈ m, f e.1 = e.2

theorem fills_complete (f : V → V) (inv : ∀ x, f (f x) = x) (ne : ∀ x, f x ≠ x)
    (d : Nat) (xs : List V) (len : xs.length ≤ d) (stable : ∀ x ∈ xs, f x ∈ xs) :
    ∃ m ∈ fills d xs, respects f m := by
  induction d generalizing xs with
  | zero =>
    have : xs = [] := by simpa using len
    subst xs
    exact ⟨[],by simp [fills],by simp [respects]⟩
  | succ d ih =>
    cases xs with
    | nil => exact ⟨[],by simp [fills],by simp [respects]⟩
    | cons x xs =>
      let y := f x
      have hy : y ∈ xs := (List.mem_cons.mp (stable x (by simp))).resolve_left (ne x)
      let rest := xs.filter fun z => z != x && z != y
      have sub : rest.length ≤ d :=
        Nat.le_trans (List.length_filter_le _ _) (Nat.le_of_succ_le_succ len)
      have closed : ∀ z ∈ rest, f z ∈ rest := by
        intro z hz
        obtain ⟨mem,neq⟩ := List.mem_filter.mp hz
        have zx : z ≠ x ∧ z ≠ y := by simpa using neq
        have ax : f z ≠ x := by
          intro h
          exact zx.2 (by simpa [y,inv] using congrArg f h)
        have ay : f z ≠ y := by
          intro h
          exact zx.1 (by simpa [y,inv] using congrArg f h)
        exact List.mem_filter.mpr ⟨(List.mem_cons.mp (stable z (by simp [mem]))).resolve_left ax,
          by simp [ax,ay]⟩
      obtain ⟨m,hm,ok⟩ := ih rest sub closed
      refine ⟨(x,y)::m,List.mem_flatMap.mpr ⟨y,hy,List.mem_map.mpr ⟨m,hm,rfl⟩⟩,?_⟩
      intro e he
      rcases List.mem_cons.mp he with rfl|mem
      · rfl
      · exact ok _ mem

def pool (c : C) := (fills 16 (free c)).map (fun m => erase (fixed c ++ m))
def actualEdges (f : V → V) : E := erase (points.map (fun x => (x,f x)))

private theorem lift_edges {f : V → V} {m : R} (h : respects f m) :
    ∀ e ∈ erase m, e ∈ actualEdges f := by
  intro e he
  obtain ⟨p,hp,hit⟩ := List.mem_filterMap.mp he
  apply List.mem_filterMap.mpr
  exact ⟨p,List.mem_map.mpr ⟨p.1,point_mem _,Prod.ext rfl (h p hp)⟩,hit⟩

theorem represented (c : C) (f : V → V) (inv : ∀ x, f (f x)=x) (ne : ∀ x, f x≠x)
    (agree : ∀ x, known c x = true → f x = partner c x) :
    ∃ m ∈ pool c, ∀ e ∈ m, e ∈ actualEdges f := by
  have symmetry : ∀ i x, known i (partner i x) = known i x := by native_decide
  have lim : ∀ i, (free i).length ≤ 16 := by native_decide
  have closed : ∀ x ∈ free c, f x ∈ free c := by
    intro x hx
    have no : known c x = false := by simpa [free] using (List.mem_filter.mp hx).2
    have also : known c (f x) = false := by
      cases eq : known c (f x) with
      | false => rfl
      | true =>
        have h := agree (f x) eq
        rw [inv] at h
        have excl := symmetry c (f x)
        rw [←h,no,eq] at excl
        contradiction
    exact List.mem_filter.mpr ⟨point_mem _,by simp [also]⟩
  obtain ⟨m,hm,ok⟩ := fills_complete f inv ne 16 (free c) (lim c) closed
  refine ⟨_,List.mem_map.mpr ⟨m,hm,rfl⟩,lift_edges ?_⟩
  intro e he
  rcases List.mem_append.mp he with head|tail
  · obtain ⟨x,_,hit⟩ := List.mem_filterMap.mp head
    split at hit
    · rename_i h
      cases hit
      exact agree x (Bool.and_eq_true_iff.mp h).1
    · contradiction
  · exact ok e tail

structure Draw where
  weight : Nat
  wild : E
  deriving Inhabited
def triple (s : Nat) : E :=
  match (List.finRange 15).filter (fun v => s.testBit v.val) with
  | [a,b,c] => [(a,b),(b,c)]
  | _ => []
def draws := (numbers (include_str "layouts.txt")).map fun row =>
  Draw.mk row[0]! ((row.drop 2).flatMap triple)
def loss (m : E) := Teams.total draws (fun g => if passes 0 (g.wild++m) then 0 else g.weight)

end VertexRedraw
