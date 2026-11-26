import FailureCounts
namespace FailureCounts
set_option interpreter.prefer_native true
theorem fixed_root : fifteen[0]! = 103452 ∧ fake15[0]! = 0 ∧
    ∀ d : Fin 5, moment fifteen d = moment fake15 d := by native_decide
theorem freely_chosen_root : sixteen[0]! = 1851792 ∧ fake16[0]! = 0 ∧
    ∀ d : Fin 4, moment sixteen d = moment fake16 d := by native_decide
#print axioms fixed_root
#print axioms freely_chosen_root
end FailureCounts
