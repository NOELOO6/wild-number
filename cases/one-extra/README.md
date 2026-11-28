# One extra edge for every K15 through K82

Let b = ⌊4⌈n/2⌉/3⌋. Every minimum proper coloring in this range has wild number b or b+1. The universal lower bound is proved separately. [Upper bound](NearRange.lean) · [Lower bound](../../verification/exact/UniversalLower.lean)

| Orders | Lower bound | Upper bound |
| --- | ---: | ---: |
| K19, K20 | 13 | 14 |
| K23, K24 | 16 | 17 |
| K27, K28 | 18 | 19 |
| K79, K80 | 53 | 54 |
| K81, K82 | 54 | 55 |

For odd n, put 3, 4 or 5 vertices in one distinguished group and split the remaining vertices into triples. Join each group by a star. A cut is a division of the vertices into two nonempty sides. It obstructs a color when no star edge and no edge of that color crosses the division.

Count each cut by its side outside the distinguished group. If that side consists of j triples, it has 3j vertices. Each color pairs all but one of the n vertices. Parity determines whether the unmatched vertex belongs to the side, so the possible sides of the correct size are counted by a single binomial coefficient. Summing over j gives an average of fewer than three obstructing cuts across all colors at each certified odd order. Some placement therefore has at most two. [Compressed count](NearCharge.lean) · [Permutation bound](../../verification/graph-bounds/UniformCuts.lean)

Any two nontrivial cuts admit an edge that crosses both. Adding that edge connects every color, using at most b+1 wild edges. The proof also transfers this bound to each following even order. [Repair argument](../../verification/graph-bounds/CutRepair.lean) · [Graph theorem](NearRange.lean)

At K43, K49, K55, K69, K75 and several other odd orders, one layout at the conjectured budget leaves at most one extra component across all colors. This also holds at the following even orders. At K75 at least 13,520 per million completions of any specified rainbow seven-vertex frame achieve it. [Component averages and complete table](piece-moments/)

At K59, K65 and K71 the conjectured budget now connects **every** color. Any prescribed pair can be reserved for the final edge. [Proof and exact counts](../absorption/)

## The remaining six to eight vertices

For every minimum proper coloring from K15 through K82 there is a set of 6, 7 or 8 vertices and a choice of exterior wild edges such that every vertex can reach this set in every color. There is enough room in the conjectured edge budget to split the set in two and draw a star in each part. This follows by reopening the two groups containing the ends of the extra edge in the earlier proof. The same result holds at the even orders by deleting one vertex and then restoring it. [Odd-order construction](TwoGroupCore.lean) · [Full range theorem](CoreRange.lean)

A split succeeds if every color already provides a path from one part to the other using that color and the fixed exterior edges. For parts of size at least three, the numbers of unordered splits are 10, 35 and 91 for core sizes 6, 7 and 8. The remaining question is whether the exterior can always be chosen to admit a successful split. [Two-group test](TwoGroupCore.lean)

The number of pieces of each color meeting the core gives a test for success. Count the connected pieces using the fixed exterior edges and the edges of that color. The entries below bound how many splits that color can prevent. If the sum for all colors is smaller than the number of splits, some split works for every color. For example, on an eight-point core each color in three pieces can block at most two splits. If every color on K23 has at most three pieces, at most 46 of the 91 splits are lost. [General bound](CoreBudget.lean) · [Six-, seven- and eight-point counts](CoreProfiles.lean)

| Core size | 1 piece | 2 pieces | 3 pieces | 4 pieces | 5 pieces | 6 pieces | 7 pieces | 8 pieces |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 6 | 0 | 1 | 1 | 2 | 4 | 10 | — | — |
| 7 | 0 | 1 | 2 | 3 | 7 | 15 | 35 | — |
| 8 | 0 | 1 | 2 | 4 | 9 | 19 | 41 | 91 |

| Coloring | Chosen core | Splits tried | Successful with this exterior | Wild number after exchanging one core vertex with one exterior vertex |
| --- | ---: | ---: | ---: | ---: |
| K19 example | 7 | 35 | 0 | [13](TwoCore19.lean) |
| K21 example | 6 | 10 | 0 | [14](TwoCore21.lean) |
| K23 example | 8 | 91 | 0 | [16](TwoCore23.lean) |

Every color reaches the chosen core in each example. For each proposed split, the certificate gives a color and a set that no edge of that color and no permitted wild edge can leave. Exchanging the two specified vertices produces a winning arrangement for the same coloring. Each example extends to the next even order with the same wild number. [How the certificates are checked](TwoCoreCheck.lean) · [Even-order transfer](CoreTransfer.lean)

A second K21 example defeats **every single exchange**, including exchanges entirely outside the core. Start with six core vertices and five exterior triples. There are 210 pairs of vertices to exchange. After each exchange, all ten possible splits of the core fail. The ten original splits also fail. Exchanging vertices 0 and 6, then 1 and 10, gives a fourteen-edge solution. Two exchanges are necessary and sufficient from this starting arrangement when the core can be split freely. [All 2,110 checks and the repair](Exchange21.lean)

There is also a K21 coloring with four exterior triples for which all 280 splits of the remaining nine vertices into three triples fail. A different layout of fourteen edges connects every color in that coloring. [Nine-point obstruction and witness](Core21Trap.lean) · [General three-group test](CoreSplit.lean)

## Deleting a vertex from an optimal even solution

Let $r$ be the vertex to delete. If no wild edge touches $r$, the even solution restricts to the odd graph. Otherwise contract any wild edge from $r$ to an ordinary vertex $a$. Remove loops and repeated edges. This saves at least one wild edge. In every color, every ordinary vertex can now reach either $a$ or the former partner of $r$. A color can therefore split into at most two components. The nonempty component on the side away from $a$ has odd size. [Contraction and path proofs](RootContraction.lean) · [Parity](RootContractionParity.lean)

One ordinary edge repairs the contraction exactly when its endpoints lie on opposite sides of every resulting cut. Count identical cuts only once. At most two distinct cuts always have a common crossing edge. For three distinct cuts there is a precise obstruction. Try the eight ways to choose one side of each cut. The contraction fails to admit a one-edge repair if and only if one of these choices gives three pairwise disjoint sets. An edge cannot touch all three disjoint sets. The converse uses the odd sizes of the three sides away from $a$ to rule out the other possible obstruction among the eight membership patterns. [Three-cut characterization](ThreeCutRepair.lean)

For $m≥5$ the solved even order $6m$ supplies the starting optimum. Therefore a counterexample at $6m-1$ would have to defeat this test for **every** optimal even drawing and **every** incident contraction. Each would produce at least three distinct cuts admitting no common crossing edge. The ordinary-kernel contraction criteria also apply at K23 when starting from the written K24 theorem. [Reduction from the infinite even family](ReverseSix.lean) · [K24 starting result](../k24/)

At each of **K23, K29, K35, K41, K47, K53, K59, K65 and K71** there is an explicit optimal layout on the next even order for which deleting the specified vertex defeats every one-edge repair. The examples use the cyclic round-robin coloring. After deletion, three pairwise disjoint nonempty sets are closed, each in its specified color. Even after filling every remaining block with all its internal edges, no added edge meets all three sets. The obstruction applies to either incident contraction when the root has two wild neighbors. It concerns this choice of even layout. [Lean graph proof](contraction-examples/ContractionExamples.lean) · [Nine layouts and cuts](contraction-examples/examples.json)

Run `./verification/graph-bounds.sh one-extra` to replay the bounds, the six-to-eight-point reduction and the examples. The ordinary kernel checks the unrestricted reduction. The small piece-count table and the explicit examples use Lean’s native evaluator.
