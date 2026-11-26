import AllStars
namespace ThreeStars
open VertexRedraw EdgeWalk WildDeletion

def liftV (x : Fin 15) : V := ⟨x.val,Nat.lt_trans x.isLt (by decide)⟩
def liftE (e : Edge 15) : Edge 16 := (liftV e.1,liftV e.2)
def completed (f : V→V) : R := points.map (fun x => (x,f x))

private theorem lift_mem {f : V→V} {e : Edge 15} (h : e∈actualEdges f) : liftE e∈completed f := by
  obtain ⟨⟨a,b⟩,mem,hit⟩ := List.mem_filterMap.mp h
  dsimp at hit
  split at hit
  · cases hit
    exact mem
  · contradiction

/-- A coloring on sixteen points gains its deleted point back on the one
ordinary line of the relevant color. All ten wild lines stay on the old points. -/
theorem restore (f : V→V) (ne : f 15≠15) (w : E) (conn : Connected (Adj (w++actualEdges f))) :
    Connected (Adj (w.map liftE ++ completed f)) := by
  let big := Adj (w.map liftE ++ completed f)
  have keep {e : Edge 15} (h : e∈w++actualEdges f) : liftE e∈w.map liftE ++ completed f := by
    rcases List.mem_append.mp h with a|b
    · exact List.mem_append_left _ (List.mem_map.mpr ⟨_,a,rfl⟩)
    · exact List.mem_append_right _ (lift_mem b)
  have old (a b : Fin 15) : Walk big (liftV a) (liftV b) := by
    exact Walk.mapInto liftV (fun _ _ h => Walk.step (.stay _) (h.imp keep keep)) (conn a b)
  have small : (f 15).val<15 := by
    have nx : (f 15).val≠15 := fun eq => ne (Fin.ext eq)
    have := (f 15).isLt
    omega
  let r : Fin 15 := ⟨(f 15).val,small⟩
  have line : big 15 (liftV r) := Or.inl (List.mem_append_right _ (List.mem_map.mpr
    ⟨15,(by decide : ∀ x : V,x∈points) _,rfl⟩))
  have project (x : V) : ∃ a : Fin 15, Walk big x (liftV a) ∧ Walk big (liftV a) x := by
    by_cases h : x.val<15
    · exact ⟨⟨x.val,h⟩,Walk.stay _,Walk.stay _⟩
    · have eq : x=15 := Fin.ext (by have := x.isLt; omega)
      subst x
      exact ⟨r,Walk.step (.stay _) line,Walk.step (.stay _) line.symm⟩
  intro x y
  obtain ⟨a,toA,_⟩ := project x
  obtain ⟨b,_,toY⟩ := project y
  exact toA.join ((old a b).join toY)

theorem both_orders (k : K) (f : C → V → V) (inv : ∀ c x, f c (f c x)=x)
    (ne : ∀ c x, f c x≠x) (proper : ∀ i j x, f i x=f j x → i=j)
    (agree : ∀ c, respects (f c) (required k c)) :
    ∃ w : E, w.length=10 ∧ w.Nodup ∧ (∀ e∈w, e.1<e.2) ∧
      ∀ c, Connected (Adj (w++actualEdges (f c))) ∧ Connected (Adj (w.map liftE++completed (f c))) := by
  obtain ⟨w,len,uniq,order,paths⟩ := three_stars k f inv ne proper agree
  exact ⟨w,len,uniq,order,fun c => ⟨paths c,restore (f c) (ne c 15) w (paths c)⟩⟩
#print axioms both_orders
end ThreeStars
