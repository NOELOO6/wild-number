import Starters27
namespace Wild27
set_option interpreter.prefer_native true
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem normalized_starters : (List.finRange 27).all check=true := by native_decide
end Wild27
