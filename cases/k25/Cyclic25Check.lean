import Starters25
namespace Wild25
set_option interpreter.prefer_native true
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem normalized_starters : (List.finRange 25).all check=true := by native_decide
end Wild25
