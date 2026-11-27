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

There is also a K21 coloring with four exterior triples for which all 280 splits of the remaining nine vertices into three triples fail. A different layout of fourteen edges connects every color in that coloring. [Nine-point obstruction and witness](Core21Trap.lean) · [General three-group test](CoreSplit.lean)

Run `./verification/graph-bounds.sh one-extra` to replay the bounds, the six-to-eight-point reduction and the examples. The ordinary kernel checks the unrestricted reduction. The small piece-count table and the explicit examples use Lean’s native evaluator.
