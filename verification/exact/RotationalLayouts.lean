import CyclicExtraction
import OrbitLayouts

namespace WildExact.Rotation
open Finset EdgeWalk WildDeletion

variable {n : Nat}
local notation "V" => Fin (n+1)
local notation "Edges" => List (Edge (n+1))

def shift (s : Edges) (c : V) : Edges := s.map fun (x,y) => (x+c,y+c)

/-- A layout checked on representatives of the color orbits supplies a wild set
whenever translation from a representative preserves the layout. -/
theorem upper_of_connected (g : Coloring (n+1) (n+1)) (odd : (n+1)%2=1)
    (v : V ≃ V) (rot : Cyclic g v) (reps : List V) (rep : V → V)
    (rep_mem : ∀ z, rep z∈reps) (s w : Edges) {budget : Nat}
    (zero : ∀ e∈s, e.1≠e.2 ∧ g.paint (v e.1) (v e.2)=missingColor g (v 0))
    (sz : w.length≤budget) (ne : ∀ e∈w, e.1≠e.2)
    (shifted : ∀ z e, e∈shift w (z-rep z) → e∈w)
    (win : ∀ c∈reps, Connected (Adj (w++shift s c))) : Upper g budget := by
  let line (e : Edge (n+1)) := (min (v e.1) (v e.2),max (v e.1) (v e.2))
  let W := w.toFinset.image line
  have stepW (a b : V) (ab : (a,b)∈w) : Touch W (v a) (v b) := by
    have h : line (a,b)∈W := mem_image_of_mem line (List.mem_toFinset.mpr ab)
    rcases le_total (v a) (v b) with l|l
    · exact Or.inl (by simpa [line,l] using h)
    · exact Or.inr (by simpa [line,l] using h)
  refine ⟨W,?_,?_,?_⟩
  · intro e he
    obtain ⟨p,hp,rfl⟩ := mem_image.mp he
    have nv : v p.1≠v p.2 := fun eq => (ne p (List.mem_toFinset.mp hp)) (v.injective eq)
    rcases lt_or_gt_of_ne nv with l|l <;> simp [line,l,l.le]
  · exact card_image_le.trans (w.toFinset_card_le.trans sz)
  let I := {i : V // i∈reps}
  apply works_of_walk_cover (I:=I) (fun i => Adj (w++shift s i.val))
    (fun i => win _ i.property)
  intro c
  obtain ⟨u,hu⟩ := (Finite.injective_iff_surjective.mp (missing_injective odd g)) c
  let z := v.symm u
  let t := z-rep z
  have rt : rep z+t=z := by dsimp [t]; rw [add_comm (rep z) (z-rep z),sub_add_cancel]
  have col : missingColor g (v z)=c := by simpa [z] using hu
  refine ⟨⟨rep z,rep_mem z⟩,fun x => v (x+t),fun y => ⟨v.symm y-t,by simp⟩,?_⟩
  have one (x y : V) (h : (x,y)∈w++shift s (rep z)) : Joined g W c (v (x+t)) (v (y+t)) := by
    rcases List.mem_append.mp h with hw'|hc
    · have mem : (x+t,y+t)∈shift w t := List.mem_map.mpr ⟨(x,y),hw',rfl⟩
      exact Or.inl (stepW _ _ (shifted z _ mem))
    · obtain ⟨⟨a,b⟩,baseEdge,eq⟩ := List.mem_map.mp hc
      change (a+rep z,b+rep z)=(x,y) at eq
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
      obtain ⟨ab,paint⟩ := zero _ baseEdge
      have edge := rot a b z ab paint
      refine Or.inr ⟨?_,?_⟩
      · exact fun eq => ab (add_right_cancel (add_right_cancel (v.injective eq)))
      · simpa only [add_assoc,rt] using edge.trans col
  intro x y e
  exact e.elim (one x y) (fun h => joined_symm g (one y x h))

/-- A layout checked on representatives of the color orbits supplies a wild set
whenever translation from a representative preserves the layout. -/
theorem upper_of_layout (g : Coloring (n+1) (n+1)) (odd : (n+1)%2=1)
    (v : V ≃ V) (rot : Cyclic g v) (reps : List V) (rep : V → V)
    (rep_mem : ∀ z, rep z∈reps) (s w : Edges) {budget : Nat}
    (zero : ∀ e∈s, e.1≠e.2 ∧ g.paint (v e.1) (v e.2)=missingColor g (v 0))
    (sz : w.length≤budget) (ne : ∀ e∈w, e.1≠e.2)
    (shifted : ∀ z e, e∈shift w (z-rep z) → e∈w)
    (win : reps.all (fun c => passes 0 (w++shift s c))=true) : Upper g budget :=
  upper_of_connected g odd v rot reps rep rep_mem s w zero sz ne shifted
    fun c hc => connected_of_passes 0 _ (List.all_eq_true.mp win c hc)

end WildExact.Rotation
