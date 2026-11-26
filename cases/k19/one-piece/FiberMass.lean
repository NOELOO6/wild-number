import Bounds
namespace WildPieces
open Finset
variable {V K : Type} [Fintype V] [DecidableEq V] [Fintype K] [DecidableEq K]

def bucketSize (f : V → K) (i : K) := (univ.filter fun x => f x = i).card

private def restrictFiber (f g : V → K) (p : {p : Equiv.Perm V // ∀ x, g (p x) = f x}) (i : K) :
    {x // f x = i} ≃ {x // g x = i} :=
  p.1.subtypeEquiv (fun x => by rw [p.2])

private def assemble (f g : V → K) (e : ∀ i, {x // f x = i} ≃ {x // g x = i}) :
    Equiv.Perm V :=
  (Equiv.sigmaFiberEquiv f).symm.trans ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv g))

private def fiberEquiv (f g : V → K) :
    {p : Equiv.Perm V // ∀ x, g (p x) = f x} ≃ (∀ i, {x // f x = i} ≃ {x // g x = i}) where
  toFun := restrictFiber f g
  invFun e := ⟨assemble f g e,fun x => (e (f x) ⟨x,rfl⟩).property⟩
  left_inv _ := by apply Subtype.ext; ext; rfl
  right_inv e := by
    funext i
    ext x
    rcases x with ⟨x,h⟩
    subst i
    rfl

/-- The number of permutations matching two lists of labels is the product of
the factorials of the label multiplicities, when those multiplicities agree. -/
theorem label_mass (f g : V → K) :
    (∑ p : Equiv.Perm V, if ∀ x, g (p x) = f x then 1 else 0) =
      if ∀ i, bucketSize f i = bucketSize g i then ∏ i, (bucketSize g i).factorial else 0 := by
  rw [Finset.sum_boole,Nat.cast_id,← Fintype.card_subtype,Fintype.card_congr (fiberEquiv f g),Fintype.card_pi]
  by_cases eq : ∀ i, bucketSize f i = bucketSize g i
  · rw [if_pos eq]
    apply Finset.prod_congr rfl
    intro i _
    have h : Fintype.card {x // f x = i} = Fintype.card {x // g x = i} := by
      simpa [Fintype.card_subtype,bucketSize] using eq i
    rw [Fintype.card_equiv (Fintype.equivOfCardEq h),h,Fintype.card_subtype]; rfl
  · rw [if_neg eq]
    obtain ⟨i,hi⟩ := Classical.not_forall.mp eq
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    apply Fintype.card_eq_zero_iff.mpr
    exact ⟨fun e => hi (by simpa [Fintype.card_subtype,bucketSize] using Fintype.card_congr e)⟩
end WildPieces
