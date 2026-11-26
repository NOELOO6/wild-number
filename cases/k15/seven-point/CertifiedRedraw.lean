import RedrawChecks
import RedrawSound
namespace RedrawModel
open VertexRedraw EdgeWalk WildDeletion Std.Tactic.BVDecide

theorem verified_checks : Checks := by
  refine ⟨checked.2.2,checked.2.1,lookups.1,?_,?_,?_⟩
  · intro i hi c
    have hc := List.all_eq_true.mp lookups.2 i (List.mem_range.mpr hi)
    exact beq_iff_eq.mp (List.all_eq_true.mp hc c ((by decide : ∀ d : C,d∈colors) _))
  · intro i hi
    have mem : groups[i]! ∈ groups.toList := by
      simp [getElem!_pos groups i hi,Array.getElem_mem]
    have h := List.all_eq_true.mp groups_valid _ mem
    simpa [Bool.and_eq_true] using h
  · intro c j hj x
    have h := List.all_eq_true.mp rows_full c ((by decide : ∀ d : C,d∈colors) c)
    have mem : row c j ∈ opts c := by simp [row,Array.getElem?_eq_getElem hj,Array.getElem_mem]
    have full := Array.all_eq_true_iff_forall_mem.mp h _ mem
    obtain ⟨y,_,eq⟩ := List.any_eq_true.mp (List.all_eq_true.mp full x ((by decide : ∀ v : V,v∈points) _))
    exact ⟨y,eq⟩

/-- The 36 exterior edges and the missing colors are fixed as in the
19-winner example. All 69 ordinary edges incident with the six marked points
can be recolored together. -/
def AllRedraws := ∀ (f : C→V→V), (∀ c x, f c (f c x)=x) → (∀ c x, f c x≠x) →
    (∀ c d, c≠d → ∀ x, f c x≠f d x) → (∀ x y : V, x≠y → ∃ c, f c x=y) →
    (∀ c x, BoundaryOptions.fixedAt lock c x=true → f c x=SixBoundary.ref c x) → Wins f

theorem of_certificate (proof : Array LRAT.IntAction) (checkedProof : LRAT.check proof formula = true) :
    AllRedraws := redraw_wins verified_checks (LRAT.check_sound proof formula checkedProof)

/-- A successful replay returns a proof of the graph statement. -/
def certify (proof : Array LRAT.IntAction) : Option (PLift AllRedraws) :=
  if ok : LRAT.check proof formula then some ⟨of_certificate proof ok⟩ else none
#print axioms of_certificate
end RedrawModel
