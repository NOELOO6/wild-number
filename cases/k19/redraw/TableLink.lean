import SevenMore
import RawMenu
namespace WildMenu
set_option interpreter.prefer_native true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem evaluated_losses : ∀ s : Finset V, RawMenu.lost (mask s) = cap s.card - value hist (mask s) := by native_decide
end WildMenu
