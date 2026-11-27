import ThirdData
namespace WildExact.Seventeen
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem reference_single : oneCount (closedTable refA.get)=8230880 := by native_decide
/-- Replay the shared cut counts and every third-matching price check for all fifteen representatives. -/
theorem all_certified : ∀ i : Fin 15, certified i=true := by native_decide

#print axioms all_certified
end WildExact.Seventeen
