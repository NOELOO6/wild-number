import LayoutData
namespace WildExact.Seventeen
theorem bigFacts : ∀ (k : Fin 16) (b : Big),
    bigStep k (bigStep k b)=b ∧ branch k (bigStep k b)=branch k b ∧
    ∀ x : V, slot (bigStep k b) (flipV k x)=flipSlot (branch k b) (slot b x) := by native_decide
theorem smallFacts : ∀ (k : Fin 12) (p : Small),
    smallStep k (smallStep k p)=p ∧ ∀ x y : Slot,
    (tag (smallStep k p) (flipSlot k x) == tag (smallStep k p) (flipSlot k y)) =
      (tag p x == tag p y) := by native_decide

end WildExact.Seventeen
