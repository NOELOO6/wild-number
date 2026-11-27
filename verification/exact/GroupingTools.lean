import Anchors
namespace WildExact
open Finset WildDeletion
variable {n : Nat}
theorem clean_row [NeZero n] (hn : n%2=1) (g : Coloring n n)
    (good : GoodThree g (atIndex n 0) (atIndex n 1) (atIndex n 2))
    (room : 6≤n) (c : Fin n) (r : Row n) (mem : r∈Rows n)
    (res : Respects (mate (augment hn g) c) r) : clean r = true := by
  let a := atIndex n 0
  let b := atIndex n 1
  let x := atIndex n 2
  have vals : a.val=0 ∧ b.val=1 ∧ x.val=2 :=
    ⟨Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)⟩
  have ab : a≠b := fun h => by have := congrArg Fin.val h; omega
  have ax : a≠x := fun h => by have := congrArg Fin.val h; omega
  have bx : b≠x := fun h => by have := congrArg Fin.val h; omega
  have ord (i j : Fin n) (ne : i≠j) :
      rowHas r (i.castSucc,j.castSucc) = decide (g.paint i j=c) := by
    rw [row_equiv _ c r mem res _ _ (fun h => ne (Fin.castSucc_injective _ h)),augment_paint]
  have star (i : Fin n) : rowHas r (i.castSucc,Fin.last n) = decide (missingColor g i=c) := by
    rw [row_equiv _ c r mem res _ _ (Fin.ne_of_lt (Fin.castSucc_lt_last _))]
    simp [augment]
  change (!((rowHas r (a.castSucc,b.castSucc) && rowHas r (x.castSucc,Fin.last n)) ||
    (rowHas r (a.castSucc,x.castSucc) && rowHas r (b.castSucc,Fin.last n)) ||
    (rowHas r (b.castSucc,x.castSucc) && rowHas r (a.castSucc,Fin.last n))))=true
  simp only [ord a b ab,ord a x ax,ord b x bx,star,Bool.not_eq_true',Bool.or_eq_false_iff,
    Bool.and_eq_false_imp,decide_eq_true_eq,decide_eq_false_iff_not]
  obtain ⟨ga,gb,gx⟩ := good
  exact ⟨⟨fun u v => ga (u.trans v.symm), fun u v => gb (u.trans v.symm)⟩,fun u v => gx (u.trans v.symm)⟩

end WildExact
