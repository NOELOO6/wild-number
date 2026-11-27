import PairTypes
import RootedMatching
namespace WildExact.Seventeen

private theorem returns (q : Equiv.Perm V) {f g : V → V} (maps : ∀ x,q (f x)=g (q x)) (k)
    (s x : V) : returnTime f s x k = returnTime g (q s) (q x) k := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => simp only [returnTime,←maps,EmbeddingLike.apply_eq_iff_eq]; split <;> simp [ih]

theorem type_symmetric (a b : V → V) : typeOf a b=typeOf b a := by
  have eq : cycleSize a b=cycleSize b a := by funext x; exact min_comm ..
  simp only [typeOf,signature,eq]

theorem type_transport (q : Equiv.Perm V) (fixes : q root=root) (a b c d : V → V)
    (ac : ∀ x,q (a x)=c (q x)) (bd : ∀ x,q (b x)=d (q x)) : typeOf a b=typeOf c d := by
  have u (x) : q ((b ∘ a) x)=(d ∘ c) (q x) := by simp [bd,ac]
  have v (x) : q ((a ∘ b) x)=(c ∘ d) (q x) := by simp [bd,ac]
  have size (x : V) : cycleSize a b x=cycleSize c d (q x) :=
    congrArg₂ min (returns q u 9 x x) (returns q v 9 x x)
  have sum (f : V → Nat) :
      ((List.finRange 18).map (fun x => f (q x))).sum=((List.finRange 18).map f).sum := by
    rw [←List.sum_toFinset _ (List.nodup_finRange _),←List.sum_toFinset _ (List.nodup_finRange _)]
    simpa using Equiv.sum_comp q f
  have eq : signature a b=signature c d := by
    simp only [signature,size,fixes,Prod.mk.injEq,true_and]
    exact sum (fun x => 1 <<< (5*cycleSize c d x))
  simp only [typeOf,eq]

theorem type_canon : ∀ i : Fin 15, typeOf first (entry (canon i).2)=i := by native_decide

end WildExact.Seventeen
