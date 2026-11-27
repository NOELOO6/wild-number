import ThreeSlots
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum

namespace WildSlots
open WildExact WildDeletion Finset
private abbrev Cell := Three × Three
private abbrev Pattern := Three ⊕ (Three ⊕ Cell)

/-- The fifteen obstructions to a matching on a three-by-three board. -/
private def pattern : Pattern → Finset Cell
  | .inl i => univ.filter (fun e => e.1=i)
  | .inr (.inl j) => univ.filter (fun e => e.2=j)
  | .inr (.inr p) => univ.filter (fun e => e.1≠p.1 ∧ e.2≠p.2)

set_option maxRecDepth 20000
set_option maxHeartbeats 0
private theorem small : ∀ h,(pattern h).card≤4 := by decide
private theorem hits : ∀ h,∀ p : Equiv.Perm Three,∃ i,(i,p i)∈pattern h := by decide
private theorem alternatives : ∀ b : Cell → Bool,
    (∃ p : Equiv.Perm Three,∀ i,b (i,p i)=true) ∨ (∃ h,∀ e∈pattern h,b e=false) := by decide

/-- One common reassignment exists if each palette of at most four colors
admits a reassignment, which may depend on that palette. -/
theorem four_colors {V C : Type} (E : C → V → V → Prop)
    (sym : ∀ c {x y},E c x y → E c y x) (u v : Three → V) :
    (∃ p : Equiv.Perm Three,passes E u v (assign p)) ↔
    ∀ S : Finset C,S.card≤4 → ∃ p : Equiv.Perm Three,
      ∀ c∈S,Connected (extend (E c) u v (assign p)) := by
  classical
  refine ⟨fun ⟨p,h⟩ _ _ => ⟨p,fun c _ => h c⟩,?_⟩
  intro localRepairs
  let ok (e : Cell) := passes E u v (cell e.1 e.2)
  rcases alternatives (fun e => decide (ok e)) with ⟨p,all⟩|⟨h,off⟩
  · exact ⟨p,(three_cells E sym u v p).mpr (fun i => of_decide_eq_true (all i))⟩
  let H := pattern h
  have witness (e : ↥H) : ∃ c,¬Connected (extend (E c) u v (cell e.val.1 e.val.2)) := by
    have no : ¬ok e.val := of_decide_eq_false (off _ e.property)
    exact Classical.not_forall.mp no
  choose who fails using witness
  let S := H.attach.image who
  have size : S.card≤4 := card_image_le.trans ((card_attach (s:=H)).le.trans (small h))
  obtain ⟨p,works⟩ := localRepairs S size
  obtain ⟨i,hi⟩ := hits h p
  let e : ↥H := ⟨(i,p i),hi⟩
  let c := who e
  have mem : c∈S := mem_image.mpr ⟨e,mem_attach _ _,rfl⟩
  have single : passes (fun _ : Unit => E c) u v (assign p) := fun _ => works c mem
  have allowed := (three_cells (fun _ : Unit => E c) (fun _ {_ _} h => sym c h) u v p).mp single i ()
  exact (fails e allowed).elim

/-- The same four-color criterion for ordinary wild-edge drawings. -/
theorem four_colors_graph {n k : Nat} (g : Coloring n k) (w : Lines n) (u v : Three → Fin n) :
    (∃ p : Equiv.Perm Three,Works g (draw w u v p)) ↔
    ∀ S : Finset (Fin k),S.card≤4 → ∃ p : Equiv.Perm Three,
      ∀ c∈S,Connected (Joined g (draw w u v p) c) := by
  simp_rw [show ∀ p c,Joined g (draw w u v p) c=extend (Joined g w c) u v (assign p) from
    fun p c => funext₂ (fun x y => propext (joined_draw g w u v p c x y))]
  simpa only [works_draw] using four_colors (Joined g w) (fun _ {_ _} h => joined_symm g h) u v

#print axioms four_colors_graph
end WildSlots
