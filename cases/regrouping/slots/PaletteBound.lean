import SlotCuts
import Mathlib.Data.Finset.Max

namespace WildSlots
open Finset WildDeletion WildExact
variable {I V C : Type}

def fits (a b : I → Bool) (p : Equiv.Perm I) := ∀ i,a i=b (p i)
instance [Fintype I] (a b : I → Bool) (p : Equiv.Perm I) : Decidable (fits a b p) :=
  inferInstanceAs (Decidable (∀ i,a i=b (p i)))

/-- Each member of a smallest cover has a permutation covered by that member alone. -/
private theorem minimal_cover {P : Type} [Fintype P] (hit : P → P → Prop)
    (covers : ∀ q,hit q q) :
    ∃ S : Finset P,(∀ q,∃ h∈S,hit h q) ∧
      ∀ h : ↥S,∃ q,∀ t : ↥S,hit t q ↔ t=h := by
  classical
  let valid (S : Finset P) := ∀ q,∃ h∈S,hit h q
  let options := (univ : Finset (Finset P)).filter valid
  have start : (univ : Finset P)∈options := mem_filter.mpr ⟨mem_univ _,fun p => ⟨p,mem_univ _,covers _⟩⟩
  obtain ⟨S,hs,minimal⟩ := options.exists_min_image card ⟨_,start⟩
  have complete := (mem_filter.mp hs).2
  refine ⟨S,complete,?_⟩
  intro h
  have fails : ¬valid (S.erase h.val) := fun H =>
    (Nat.not_le_of_lt (card_erase_lt_of_mem h.property)) (minimal _ (mem_filter.mpr ⟨mem_univ _,H⟩))
  unfold valid at fails
  push_neg at fails
  obtain ⟨q,privateQ⟩ := fails
  obtain ⟨x,hx,yes⟩ := complete q
  have only (y : ↥S) (good : hit y q) : y=h := by
    apply Subtype.ext
    exact Classical.byContradiction (fun ne => privateQ _ (mem_erase.mpr ⟨ne,y.property⟩) good)
  have eq := only ⟨x,hx⟩ yes
  refine ⟨q,fun t => ⟨only t,?_⟩⟩
  intro eqt
  simpa [←show x=h.val from congrArg Subtype.val eq,eqt] using yes

/-- A bound on irredundant covers by binary cuts gives the same bound on
the number of colors needed to witness a failed reassignment. -/
theorem palette_from_covers [Fintype I] (d : Nat)
    (bound : ∀ (H : Finset (Equiv.Perm I)) (a b : ↥H → I → Bool),
      (∀ q,∃ h,fits (a h) (b h) q) →
      (∀ h,∃ q,∀ t,fits (a t) (b t) q ↔ t=h) → H.card≤d)
    (E : C → V → V → Prop) (sym : ∀ c {x y},E c x y → E c y x) (u v : I → V) :
    (∃ p : Equiv.Perm I,passes E u v (assign p)) ↔
      ∀ S : Finset C,S.card≤d → ∃ p : Equiv.Perm I,∀ c∈S,Connected (extend (E c) u v (assign p)) := by
  classical
  refine ⟨fun ⟨p,ok⟩ _ _ => ⟨p,fun c _ => ok c⟩,?_⟩
  intro localRepairs
  by_contra none
  have block (p : Equiv.Perm I) : ∃ a : I → Bool,∃ c,
      ¬Connected (extend (E c) u v (fun i j => a i=a (p.symm j))) := by
    have bad : ¬passes E u v (assign p) := fun h => none ⟨p,h⟩
    rw [all_splits E sym u v p] at bad
    simpa only [passes,not_forall] using bad
  choose a color bad using block
  let b (p : Equiv.Perm I) (j : I) := a p (p.symm j)
  obtain ⟨H,cover,priv⟩ := minimal_cover (fun h q => fits (a h) (b h) q)
    (fun p i => by simp [b])
  let chosen := H.image color
  have size := bound H (fun h => a h) (fun h => b h)
    (fun q => by obtain ⟨h,mem,yes⟩ := cover q; exact ⟨⟨h,mem⟩,yes⟩) priv
  obtain ⟨p,ok⟩ := localRepairs chosen (card_image_le.trans size)
  obtain ⟨h,mem,matchCut⟩ := cover p
  have single : passes (fun _ : Unit => E (color h)) u v (assign p) := fun _ =>
    ok (color h) (mem_image.mpr ⟨h,mem,rfl⟩)
  exact bad h (passes_mono (Q:=fun i j => a h i=b h j)
    (fun i j (eq : p i=j) => eq ▸ matchCut i) single ())

end WildSlots
