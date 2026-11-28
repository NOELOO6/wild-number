import Numeric
import Lean.Elab.Term

namespace WildSieve
open Lean Elab Term

/-- Construct candidate integer tables at elaboration time. The resulting term
is a list of numerals. Each inequality is then proved by kernel reduction. -/
elab "sieveTables%(" low:num "," count:num ")" : term => do
  let cases := (List.range count.getNat).map fun i =>
    let n := low.getNat + 2*i
    (n, makeTable n (fixedSize n) (levels n))
  return toExpr cases

set_option maxHeartbeats 0
set_option maxRecDepth 200000

/-- Each order has its own kernel check so reduction can release the
working memory before starting the next order. -/
structure CheckedOrder where
  order : Nat
  table : Array Nat
  passed : tablePasses order (fixedSize order) (levels order) table=true

elab "sieveTable%(" n:num ")" : term =>
  let k := n.getNat
  return toExpr (makeTable k (fixedSize k) (levels k))

end WildSieve
