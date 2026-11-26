import StarRows
import GeometryRows
import StarBounds
namespace ThreeStars
open VertexRedraw EdgeWalk WildDeletion Teams

/-- Only the colors on edges incident to the three ordinary points and the
missing-color point are prescribed. All other pairs may be colored freely. -/
theorem three_stars (k : K) (f : C → V → V) (inv : ∀ c x, f c (f c x)=x)
    (ne : ∀ c x, f c x≠x) (proper : ∀ i j x, f i x=f j x → i=j)
    (agree : ∀ c, respects (f c) (required k c)) :
    ∃ w : E, w.length=10 ∧ w.Nodup ∧ (∀ e∈w, e.1<e.2) ∧
      ∀ c, Connected (Adj (w ++ actualEdges (f c))) := by
  classical
  let gs := layouts k
  have repr (c : C) := represent k c (f c) (inv c) (ne c) (agree c)
  let m := fun c => Classical.choose (repr c)
  have spec (c) : m c∈candidates k c ∧ respects (f c) (m c) := Classical.choose_spec (repr c)
  obtain ⟨main,okEdges⟩ := Bool.and_eq_true_iff.mp (checked k)
  obtain ⟨budgets,room⟩ := Bool.and_eq_true_iff.mp main
  have each (c : C) := Bool.and_eq_true_iff.mp (List.all_eq_true.mp
    (List.all_eq_true.mp budgets c ((by decide : ∀ i : C, i∈colors) c)) (m c) (spec c).1)
  let charge := fun c => spent (ledger gs) (m c)
  have upper : total colors charge ≤ total colors (fun c => (costs k)[c.val]! + total (m c) (fee k)) :=
    total_mono _ _ _ (fun c _ => of_decide_eq_true (each c).2)
  rw [total_add] at upper
  have fees := fees_bounded k m f proper (fun c => (spec c).2) (fun c => (each c).1)
  have room' := of_decide_eq_true room
  obtain ⟨g,hg,works⟩ := FiveColors.weighted_survivor gs colors Layout.weight
    (fun g c => spoils g (m c)) charge (fun c _ => loss_bounded gs (m c)) (by
      change total colors charge < total (layouts k) Layout.weight
      omega)
  obtain ⟨len,nodup,sorted⟩ := of_decide_eq_true (List.all_eq_true.mp okEdges g hg)
  refine ⟨wild g,len,nodup,sorted,?_⟩
  intro c
  have isFull := beq_iff_eq.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (each c).1).1).1
  exact path_of_unblocked g (List.all_eq_true.mp (geometric k) g hg) (m c) isFull
    (f c) (inv c) (ne c) (spec c).2 (works c ((by decide : ∀ i : C, i∈colors) c))
#print axioms three_stars
end ThreeStars
