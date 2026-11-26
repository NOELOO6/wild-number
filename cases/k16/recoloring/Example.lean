import Recolor
namespace SixExample
open SixColors EdgeWalk WildDeletion
def replacement : List Raw := [
  [(0,10), (1,5), (2,4), (3,15), (6,13), (7,8), (9,12), (11,14)],
  [(0,8), (1,9), (2,13), (3,12), (4,6), (5,15), (7,14), (10,11)],
  [(0,4), (1,3), (2,15), (5,14), (6,9), (7,10), (8,13), (11,12)],
  [(0,15), (1,7), (2,6), (3,14), (4,13), (5,12), (8,11), (9,10)],
  [(0,6), (1,15), (2,8), (3,5), (4,11), (7,12), (9,14), (10,13)],
  [(0,2), (1,14), (3,7), (4,15), (5,10), (6,11), (8,9), (12,13)]]
def newColoring := replacement ++ ((List.range' 6 9).map original)
def layout := erasePoint 15 (chains [0,4,5,1,3,9,2,6,7,8,12,14,10,11,13])
def genuine (m : Raw) := m.length == 8 && (List.range 16).all fun v =>
  m.any (fun (a,b) => a == v || b == v)
theorem actual_coloring : newColoring.length = 15 ∧ newColoring.all genuine = true ∧
    ((List.range 16).all fun b => (List.range b).all fun a =>
      newColoring.any (fun m => m.contains (a,b))) = true ∧
    (replacement.all fun m => ((List.range 15).all fun c => bits m != bits (original c))) = true := by native_decide
theorem ten_lines : layout.length = 10 ∧
    ∀ m ∈ newColoring, Connected (Adj (layout++erasePoint 15 m)) := by
  have h : newColoring.all (fun m => passes 0 (layout++erasePoint 15 m)) = true := by native_decide
  exact ⟨by decide,fun m hm => connected_of_passes 0 _ (List.all_eq_true.mp h m hm)⟩
#print axioms ten_lines
abbrev V := Fin 16
abbrev C := Fin 15
def locate (c : C) (v : V) : V :=
  let e := (newColoring[c.val]!.find? fun (a,b) => a == v.val || b == v.val).getD (0,0)
  ⟨(if e.1 == v.val then e.2 else e.1)%16, Nat.mod_lt _ (by decide)⟩
def partners := ((List.finRange 15).map fun c => ((List.finRange 16).map (locate c)).toArray).toArray
def mate (c : C) (v : V) := partners[c.val]![v.val]!
def along (a b : C) (v : V) : Nat → V
  | 0 => v
  | k+1 => mate (if k%2 == 0 then a else b) (along a b v k)
def ranks := ((List.finRange 16).map (fun v => (List.range 16).findIdx (fun k => along 2 0 0 k == v))).toArray
def rank (v : V) := ranks[v.val]!
theorem spanning_cycle : ∀ v : V, along 2 0 0 (rank v) = v := by native_decide

def images (a b : C) (v : V) := ((List.finRange 16).map (fun x => along a b v (rank x))).toArray
def readImage (t : Array V) (v : V) := t[v.val]!
def keepsColors (t : Array V) := (List.finRange 15).all fun c => (List.finRange 15).any fun d =>
  (List.finRange 16).all fun v => readImage t (mate c v) == mate d (readImage t v)
def distinct (t : Array V) := (List.finRange 16).all fun v => (List.finRange 16).all fun u =>
  v == u || readImage t v != readImage t u
theorem only_identity : ∀ a b : C, ∀ v : V, let t := images a b v
    (distinct t && keepsColors t) = true → ∀ u : V, readImage t u = u := by native_decide
theorem image_entry : ∀ a b : C, ∀ v x : V, readImage (images a b v) x = along a b v (rank x) := by native_decide

/-- Every injective renaming that permutes colors fixes every vertex. -/
theorem asymmetric (f : V → V) (σ : C → C) (inj : ∀ x y, f x = f y → x = y)
    (maps : ∀ c x, f (mate c x) = mate (σ c) (f x)) : ∀ x, f x = x := by
  have follow : ∀ k, f (along 2 0 0 k) = along (σ 2) (σ 0) (f 0) k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => simp only [along]; split <;> rw [maps,ih]
  let t := images (σ 2) (σ 0) (f 0)
  have agree (x : V) : readImage t x = f x := by
    rw [image_entry, ← follow,spanning_cycle]
  have hd : distinct t = true := by
    apply List.all_eq_true.mpr
    intro x _
    apply List.all_eq_true.mpr
    intro y _
    by_cases eq : x = y
    · simp [eq]
    · have ne : f x ≠ f y := fun h => eq (inj x y h)
      simp [agree, eq, ne]
  have each : ∀ k : C, k ∈ List.finRange 15 := by decide
  have hc : keepsColors t = true := by
    apply List.all_eq_true.mpr
    intro c _
    apply List.any_eq_true.mpr
    refine ⟨σ c,each _,List.all_eq_true.mpr ?_⟩
    intro v _
    simp [agree,maps]
  exact fun x => (agree x).symm.trans (only_identity _ _ _ (Bool.and_eq_true_iff.mpr ⟨hd,hc⟩) x)
#print axioms asymmetric
end SixExample
