import Starters21

namespace Wild21
set_option interpreter.prefer_native true
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem every_starter_passes : scan acceptsStarter 10 points.tail [] [] = true := by native_decide

end Wild21
