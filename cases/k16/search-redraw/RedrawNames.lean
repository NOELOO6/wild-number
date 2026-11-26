import RedrawGraph
namespace SearchRedraw
open EdgeWalk WildDeletion
def masks := Std.HashSet.ofList (plans.map Plan.mask)
def six (m : Nat) := ((List.range 15).filter m.testBit).length
theorem cover_lookup : (List.range 32768).all (fun m => six m != 6 ||
    symmetries.any (fun s => validSym s && masks.contains (move s m))) = true := by native_decide

theorem every_mask {m : Nat} (hm : m<32768) (h6 : six m=6) :
    ∃ s∈symmetries, validSym s=true ∧ ∃ p∈plans, p.mask=move s m := by
  have hit := List.all_eq_true.mp cover_lookup m (List.mem_range.mpr hm)
  simp only [h6,bne_self_eq_false,Bool.false_or] at hit
  obtain ⟨s,hs,ok⟩ := List.any_eq_true.mp hit
  obtain ⟨valid,found⟩ := Bool.and_eq_true_iff.mp ok
  unfold masks at found
  rw [Std.HashSet.contains_ofList] at found
  obtain ⟨p,hp,eq⟩ := List.mem_map.mp (List.contains_iff_mem.mp found)
  exact ⟨s,hs,valid,p,hp,eq⟩

def orderLine (f : Fin 15 → Fin 15) (e : Edge 15) : Edge 15 :=
  if f e.1 ≤ f e.2 then (f e.1,f e.2) else (f e.2,f e.1)
def rename (f : Fin 15 → Fin 15) (es : Edges) := es.map (orderLine f)

private theorem step_name (f : Fin 15 → Fin 15) (es : Edges) {x y} (he : Adj es x y) :
    Adj (rename f es) (f x) (f y) := by
  have edge {a b} (h : (a,b)∈es) : Adj (rename f es) (f a) (f b) := by
    have mem := List.mem_map_of_mem (f:=orderLine f) h
    by_cases v : f a ≤ f b
    · exact Or.inl (by simpa [rename,orderLine,v] using mem)
    · exact Or.inr (by simpa [rename,orderLine,v] using mem)
  exact he.elim edge (fun h => (edge h).symm)

/-- A solution on any checked representative gives a solution after any
bijective relabeling of its points. Lines are put back in ascending order. -/
theorem transport (f back : Fin 15 → Fin 15) (inv : ∀ v, f (back v)=v)
    (colors : List Edges) (w : Edges) (len : w.length=10)
    (paths : ∀ m∈colors, Connected (Adj (w++m))) :
    ∃ u : Edges, u.length=10 ∧ ∀ m∈colors.map (rename f), Connected (Adj (u++m)) := by
  refine ⟨rename f w,by simpa [rename] using len,?_⟩
  intro m hm x y
  obtain ⟨old,listed,rfl⟩ := List.mem_map.mp hm
  have h := (paths old listed (back x) (back y)).mapInto f (F:=Adj (rename f (w++old)))
      (fun a b e => Walk.step (.stay _) (step_name f _ e))
  simpa only [inv,rename,List.map_append] using h
def roundRobin := (List.range 15).map fun c => (Array.range 16).map fun x =>
  if x=15 then c else if x=c then 15 else (2*c+15-x)%15
def singleCycle (a b : Array Nat) := Id.run do
  let mut v := 0
  let mut seen := 0
  for _ in [:8] do
    let w := a[v]!
    seen := seen ||| 2^v ||| 2^w
    v := b[w]!
  return seen == 65535
def cycleCount (ms : List (Array Nat)) := (ms.zipIdx.map (fun (a,i) =>
  ((ms.take i).filter (fun b => singleCycle a b)).length)).sum
theorem distinct_starts : SearchExample.valid = true ∧
    cycleCount SearchExample.rows = 55 ∧ cycleCount roundRobin = 60 := by native_decide
#print axioms every_mask
#print axioms transport
end SearchRedraw
