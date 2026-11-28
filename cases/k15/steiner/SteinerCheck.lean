import SteinerLayouts

namespace Wild15.Steiner
set_option interpreter.prefer_native true
set_option maxRecDepth 30000
set_option maxHeartbeats 0

theorem exhaustive : lengths.all exhaust=true := by native_decide

end Wild15.Steiner
