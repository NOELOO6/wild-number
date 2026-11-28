# Two prescribed triples on a seven-point set

Fix the root and six ordinary points such that each color has at most two matching edges on those seven points. **Every split of the six into two prescribed triples can be completed while clearing every ordinary two-triple cut.** Moreover, one can prescribe an entire partition of the other nine points into three triples to avoid. The completion uses none of the three excluded triples.

In particular each split has two completions without a common exterior triple. Choose the first completion and exclude its three exterior triples when finding the second. At least 1,540 choices of the six points meet the hypothesis for every specified root in every one-factorization. Thus the statement applies to all ten splits on each of those choices, even to a starting triple closed together with the root. Root cuts still have to be addressed for full connectivity. [Seven-point existence theorem](../../k16/seven-count.md)

## Reduction to nine points

Call the fixed triples $A,B$ and the nine remaining points $Y$. An ordinary two-triple cut cannot close $A\cup B$, since that would put three matching edges inside the seven. For each color mark an exterior triple $T$ if the color closes $A\cup T$, $B\cup T$ or $Y\setminus T$. A partition of $Y$ avoiding all marks clears every ordinary two-triple cut. In the last case the other two exterior triples make the closed side.

For a subset $S\subseteq Y$ of size $k$, give $T$ weight $w_{|S\cap T|}$. The following table bounds the total weight of all marked triples, counting a triple once per color that marks it. The last column bounds the additional weight when the three triples of any prescribed partition of $Y$ are added to the forbidden family.

| $k$ | Weights for intersections of size 0, 1, 2, 3 | Marked weight at most | Additional weight at most |
| ---: | --- | ---: | ---: |
| 0 | 1, 1, 1, 1 | 37 | 3 |
| 3 | 3, 2, 0, 0 | 82 | 6 |
| 1 | 0, 1, 0, 0 | 25 | 1 |
| 1 | 1, 0, 0, 0 | 31 | 2 |
| 3 | 0, 1, 2, 2 | 51 | 3 |
| 4 | 0, 0, 1, 1 | 29 | 2 |
| 4 | 2, 0, 3, 0 | 98 | 8 |

The extra weights follow by distributing the $k$ points of $S$ across the three excluded triples. To prove the marked-weight bounds, classify vertices into the five sets $\{z\},A,B,S,Y\setminus S$. For each row, the Lean certificate assigns integer prices to the fifteen possible unordered pairs of vertex types and a constant price to each color. For every matching meeting the seven-point hypothesis it checks that the priced matching covers the weighted marks of that color, after multiplying by the row denominator. Summing over colors charges every edge of K16 exactly once. Grouping still-unused partners by their types covers all matchings up to permutations within the five sets. [Lean prices and matching checks](NineOrdinary15.lean)

The forbidden family after the three exclusions has at most 40 triples. If it met every partition of $Y$, it would contain a minimal blocker from the nine-point catalogue, up to a relabeling. There are 89 entries of size at most 40. For each, Lean finds a row and a subset $S$ where the blocker's weight exceeds the sum of the last two columns. All triple weights are nonnegative, so containment is impossible. The matching and catalogue checks use Lean's native evaluator. The reduction of the coloring and the sum of the edge prices are the written argument above. [Nine-point catalogue and coverage proof](../endgame/) · [Lean exclusion check](NineOrdinary15.lean)

From the repository root, `./verification/replay.sh k15` checks the matching prices and the catalogue exclusions after rebuilding the nine-point catalogue.
