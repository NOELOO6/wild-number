import Starters23

namespace Wild23
open WildExact.Rotation
set_option interpreter.prefer_native true
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem every_starter_passes : scan acceptsStarter 11 (List.finRange 23).tail [] [] = true := by
  native_decide

end Wild23
