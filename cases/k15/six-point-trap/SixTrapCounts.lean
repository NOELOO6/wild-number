import SixTrap
namespace SixTrap
/-- Each counted win uses fifteen successful graph searches. Each counted loss
has a separating set checked against every edge of a failed color. -/
theorem exhaustive : visit ordinary 4 32767 [] {} = ⟨127413,1273987,0⟩ := by native_decide
#print axioms every_fixed_six_loses
#print axioms one_exchange_works
#print axioms exhaustive
end SixTrap
