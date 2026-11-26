import Separate19
namespace Separate19
set_option interpreter.prefer_native true
set_option maxHeartbeats 0
theorem completions : shapes3.all (fun (a,b,c,n) => count a b c == n) = true := by native_decide
theorem prices_work : (Array.range 22).all audit = true := by native_decide
#print axioms completions
#print axioms prices_work
end Separate19
