import Switches
namespace SevenSwitch
set_option interpreter.prefer_native true
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem inputs : fixedLayouts.size = 512 ∧ movingLayouts.size = 512 ∧
    fixedLayouts.all (goodLayout 15) = true ∧ movingLayouts.all (goodLayout 0) = true ∧
    wins.size = 2027025 ∧ wins[rank fixedColor fixedColor 0]! = allBits ∧
    as.size = 19876 ∧ pairCount = 797448 := by native_decide

theorem all_switches : ∀ i : Fin 8, covered i.val = true := by native_decide

#print axioms inputs
#print axioms all_switches
end SevenSwitch
